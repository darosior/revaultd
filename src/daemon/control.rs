//! By itself, the daemon is not doing much: it basically just keeps its database updated with the
//! chain events in the bitcoind thread.
//! Any process is at first initiated by a manual interaction. This interaction is possible using the
//! JSONRPC api, which events are handled in the RPC thread.
//!
//! The main thread handles and coordinates all processes, which (for now) all originates from a
//! command sent to the RPC server. This control handling is what happens here.

use crate::{
    assert_tx_type,
    bitcoind::BitcoindError,
    database::{
        actions::db_store_revocation_txs,
        interface::{db_tip, db_transactions, db_vault_by_deposit, db_vaults},
        schema::RevaultTx,
        DatabaseError,
    },
    revaultd::{BlockchainTip, RevaultD, VaultStatus},
    threadmessages::*,
};
use common::{assume_ok, assume_some};

use revault_net::{
    message::server::{GetSigs, RevaultSignature, Sig, Sigs},
    sodiumoxide,
    transport::KKTransport,
};
use revault_tx::{
    bitcoin::{secp256k1::Signature, Network, OutPoint, Txid, PublicKey as BitcoinPubKey},
    transactions::{
        transaction_chain, CancelTransaction, EmergencyTransaction, RevaultTransaction,
        UnvaultEmergencyTransaction, UnvaultTransaction,
    },
    txins::VaultTxIn,
    txouts::VaultTxOut,
};

use std::{
    collections::BTreeMap,
    fmt,
    path::PathBuf,
    process,
    sync::{
        mpsc::{self, Receiver, RecvError, SendError, Sender},
        Arc, RwLock,
    },
    thread,
    thread::JoinHandle,
};

/// Any error that could arise during the process of executing the user's will.
/// Usually fatal.
#[derive(Debug)]
pub enum ControlError {
    ChannelCommunication(String),
    Database(String),
    Bitcoind(String),
    TransactionManagement(String),
}

impl fmt::Display for ControlError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}", self)
    }
}

impl std::error::Error for ControlError {}

impl<T> From<SendError<T>> for ControlError {
    fn from(e: SendError<T>) -> Self {
        Self::ChannelCommunication(format!("Sending to channel: '{}'", e))
    }
}

impl From<RecvError> for ControlError {
    fn from(e: RecvError) -> Self {
        Self::ChannelCommunication(format!("Receiving from channel: '{}'", e))
    }
}

impl From<DatabaseError> for ControlError {
    fn from(e: DatabaseError) -> Self {
        Self::Database(format!("Database error: {}", e))
    }
}

impl From<BitcoindError> for ControlError {
    fn from(e: BitcoindError) -> Self {
        Self::Bitcoind(format!("Bitcoind error: {}", e))
    }
}

impl From<revault_tx::Error> for ControlError {
    fn from(e: revault_tx::Error) -> Self {
        Self::TransactionManagement(format!("Revault transaction error: {}", e))
    }
}

// Ask bitcoind for a wallet transaction
fn bitcoind_wallet_tx(
    bitcoind_tx: &Sender<BitcoindMessageOut>,
    txid: Txid,
) -> Result<Option<WalletTransaction>, ControlError> {
    log::trace!("Sending WalletTx to bitcoind thread for {}", txid);

    let (bitrep_tx, bitrep_rx) = mpsc::sync_channel(0);
    bitcoind_tx.send(BitcoindMessageOut::WalletTransaction(txid, bitrep_tx))?;
    bitrep_rx.recv().map_err(|e| e.into())
}

// List the vaults from DB, and filter out the info the RPC wants
// FIXME: we could make this more efficient with smarter SQL queries
fn listvaults_from_db(
    revaultd: &RevaultD,
    statuses: Option<Vec<VaultStatus>>,
    outpoints: Option<Vec<OutPoint>>,
) -> Result<Vec<ListVaultsEntry>, DatabaseError> {
    db_vaults(&revaultd.db_file()).map(|db_vaults| {
        db_vaults
            .into_iter()
            .filter_map(|db_vault| {
                if let Some(ref statuses) = statuses {
                    if !statuses.contains(&db_vault.status) {
                        return None;
                    }
                }

                if let Some(ref outpoints) = &outpoints {
                    if !outpoints.contains(&db_vault.deposit_outpoint) {
                        return None;
                    }
                }

                let address = revaultd.vault_address(db_vault.derivation_index);
                Some(ListVaultsEntry {
                    amount: db_vault.amount,
                    status: db_vault.status,
                    deposit_outpoint: db_vault.deposit_outpoint,
                    derivation_index: db_vault.derivation_index,
                    address,
                })
            })
            .collect()
    })
}

// List all the transactions of all the vaults which deposit outpoints we are passed. If we don't
// have the fully signed transaction in db, we create an unsigned one.
fn txlist_from_outpoints(
    revaultd: &RevaultD,
    bitcoind_tx: &Sender<BitcoindMessageOut>,
    outpoints: Option<Vec<OutPoint>>,
) -> Result<Vec<VaultTransactions>, ControlError> {
    let xpub_ctx = revaultd.xpub_ctx();
    let db_file = &revaultd.db_file();

    // If they didn't provide us with a list of outpoints, catch'em all!
    let db_vaults = if let Some(outpoints) = outpoints {
        // FIXME: we can probably make this more efficient with some SQL magic
        let mut vaults = Vec::with_capacity(outpoints.len());
        for outpoint in outpoints.iter() {
            if let Some(vault) = db_vault_by_deposit(db_file, &outpoint)? {
                vaults.push(vault);
            }
            // FIXME: Invalid outpoints are siltently ignored..
        }
        vaults
    } else {
        db_vaults(db_file)?
    };

    let mut tx_list = Vec::with_capacity(db_vaults.len());
    for db_vault in db_vaults {
        let outpoint = db_vault.deposit_outpoint;
        let deriv_index = db_vault.derivation_index;
        let mut txs = db_transactions(db_file, db_vault.id, &[])?.into_iter();

        let deposit = assume_some!(
            bitcoind_wallet_tx(&bitcoind_tx, outpoint.txid)?,
            "Vault without deposit tx in db for {}",
            &outpoint,
        );

        // Get the descriptors in case we need to derive the transactions (not signed
        // yet, ie not in DB).
        // One day, we could try to be smarter wrt free derivation but it's not
        // a priority atm.
        let deposit_descriptor = revaultd.vault_descriptor.derive(deriv_index);
        let vault_txin = VaultTxIn::new(
            db_vault.deposit_outpoint,
            VaultTxOut::new(db_vault.amount.as_sat(), &deposit_descriptor, xpub_ctx),
        );
        let unvault_descriptor = revaultd.unvault_descriptor.derive(deriv_index);
        let cpfp_descriptor = revaultd.cpfp_descriptor.derive(deriv_index);
        let emer_address = revaultd.emergency_address.clone();

        // We can always re-generate the Unvault out of the descriptor if it's
        // not in DB..
        let mut unvault_tx = txs
            .find(|db_tx| matches!(db_tx.psbt, RevaultTx::Unvault(_)))
            .map(|tx| assert_tx_type!(tx.psbt, Unvault, "We just found it"))
            .unwrap_or(UnvaultTransaction::new(
                vault_txin.clone(),
                &unvault_descriptor,
                &cpfp_descriptor,
                xpub_ctx,
                revaultd.lock_time,
            )?);
        let unvault_txin = unvault_tx
            .unvault_txin(&unvault_descriptor, xpub_ctx, revaultd.unvault_csv)
            .expect("Just created it");
        let wallet_tx = bitcoind_wallet_tx(
            &bitcoind_tx,
            unvault_tx.inner_tx().global.unsigned_tx.txid(),
        )?;
        // The transaction is signed if we did sign it, or if others did (eg
        // non-stakeholder managers) and we noticed it from broadcast.
        // TODO: maybe a is_finalizable upstream ? finalize() is pretty costy
        let is_signed = unvault_tx.finalize(&revaultd.secp_ctx).is_ok() || wallet_tx.is_some();
        let unvault = TransactionResource {
            wallet_tx,
            tx: unvault_tx,
            is_signed,
        };

        // .. But not the spend, as it's dynamically chosen by the managers and
        // could be anything!
        let spend = if let Some(mut tx) = txs
            .find(|db_tx| matches!(db_tx.psbt, RevaultTx::Spend(_)))
            .map(|tx| assert_tx_type!(tx.psbt, Spend, "We just found it"))
        {
            let wallet_tx =
                bitcoind_wallet_tx(&bitcoind_tx, tx.inner_tx().global.unsigned_tx.txid())?;
            // TODO: maybe a is_finalizable upstream ? finalize() is pretty costy
            let is_signed = tx.finalize(&revaultd.secp_ctx).is_ok() || wallet_tx.is_some();
            Some(TransactionResource {
                wallet_tx,
                tx,
                is_signed,
            })
        } else {
            None
        };

        // The cancel transaction is deterministic, so we can always return it.
        let mut cancel_tx = txs
            .find(|db_tx| matches!(db_tx.psbt, RevaultTx::Cancel(_)))
            .map(|tx| assert_tx_type!(tx.psbt, Cancel, "We just found it"))
            .unwrap_or_else(|| {
                CancelTransaction::new(
                    unvault_txin.clone(),
                    None,
                    &deposit_descriptor,
                    xpub_ctx,
                    revaultd.lock_time,
                )
            });
        let wallet_tx =
            bitcoind_wallet_tx(&bitcoind_tx, cancel_tx.inner_tx().global.unsigned_tx.txid())?;
        // TODO: maybe a is_finalizable upstream ? finalize() is pretty costy
        let is_signed = cancel_tx.finalize(&revaultd.secp_ctx).is_ok() || wallet_tx.is_some();
        let cancel = TransactionResource {
            wallet_tx,
            tx: cancel_tx,
            is_signed,
        };

        // The emergency transaction is deterministic, so we can always return it.
        let mut emergency_tx = txs
            .find(|db_tx| matches!(db_tx.psbt, RevaultTx::Emergency(_)))
            .map(|tx| assert_tx_type!(tx.psbt, Emergency, "We just found it"))
            .unwrap_or_else(|| {
                EmergencyTransaction::new(vault_txin, None, emer_address, revaultd.lock_time)
                    .unwrap() // FIXME
            });
        let wallet_tx = bitcoind_wallet_tx(
            &bitcoind_tx,
            emergency_tx.inner_tx().global.unsigned_tx.txid(),
        )?;
        // TODO: maybe a is_finalizable upstream ? finalize() is pretty costy
        let is_signed = emergency_tx.finalize(&revaultd.secp_ctx).is_ok() || wallet_tx.is_some();
        let emergency = TransactionResource {
            wallet_tx,
            tx: emergency_tx,
            is_signed,
        };

        // Same for the second emergency.
        let mut unvault_emergency_tx = txs
            .find(|db_tx| matches!(db_tx.psbt, RevaultTx::UnvaultEmergency(_)))
            .map(|tx| assert_tx_type!(tx.psbt, UnvaultEmergency, "We just found it"))
            .unwrap_or_else(|| {
                UnvaultEmergencyTransaction::new(
                    unvault_txin,
                    None,
                    revaultd.emergency_address.clone(),
                    revaultd.lock_time,
                )
            });
        let wallet_tx = bitcoind_wallet_tx(
            &bitcoind_tx,
            unvault_emergency_tx.inner_tx().global.unsigned_tx.txid(),
        )?;
        // TODO: maybe a is_finalizable upstream ? finalize() is pretty costy
        let is_signed =
            unvault_emergency_tx.finalize(&revaultd.secp_ctx).is_ok() || wallet_tx.is_some();
        let unvault_emergency = TransactionResource {
            wallet_tx,
            tx: unvault_emergency_tx,
            is_signed,
        };

        tx_list.push(VaultTransactions {
            outpoint,
            deposit,
            unvault,
            spend,
            cancel,
            emergency,
            unvault_emergency,
        });
    }

    Ok(tx_list)
}

// Encrypt an Emergency transaction signature to a stakeholder's public key. This is a
// hack to mitigate a possible DOS with Emergency signatures transiting in clear. See
// practical-revault for details.
// FIXME: eventually use precomputed() from libsodium to avoid unnecessary work. Or get
// rid of this dirty workaround altogether.
fn encrypt_emergency_sig(
    sig: &[u8],
    pk: &sodiumoxide::crypto::box_::PublicKey,
    sk: &sodiumoxide::crypto::box_::SecretKey,
) -> Vec<u8> {
    // Init is called at startup, it's fine.
    let nonce = sodiumoxide::crypto::box_::gen_nonce();
    sodiumoxide::crypto::box_::seal(sig, &nonce, pk, sk)
}

// Decrypt a signature encrypted with `encrypt_emergency_sig`.
fn decrypt_emergency_sig(
    sig: &[u8],
    pk: &sodiumoxide::crypto::box_::PublicKey,
    sk: &sodiumoxide::crypto::box_::SecretKey,
) -> Vec<u8> {
    // Init is called at startup, it's fine.
    let nonce = sodiumoxide::crypto::box_::gen_nonce();
    sodiumoxide::crypto::box_::open(sig, &nonce, pk, sk)
}

// Dump all the signatures from these PSBTs to the sync server.
fn share_signatures(
    revaultd: Arc<RwLock<RevaultD>>,
    cancel_tx: CancelTransaction,
    emer_tx: EmergencyTransaction,
    unvault_emer_tx: UnvaultEmergencyTransaction,
) -> Result<(), Box<dyn std::error::Error>> {
    let revaultd = revaultd.read().unwrap();
    let mut transport = KKTransport::connect(
        revaultd.coordinator_host,
        &revaultd.noise_secret,
        &revaultd.coordinator_noisekey,
    )?;
    let cancel_sigs = cancel_tx
        .inner_tx()
        .inputs
        .get(0)
        .expect("Cancel tx has a single input, inbefore fee bumping.")
        .partial_sigs
        .clone();
    let emer_sigs = emer_tx
        .inner_tx()
        .inputs
        .get(0)
        .expect("Emergency tx has a single input, inbefore fee bumping.")
        .partial_sigs
        .clone();
    let unvault_emer_sigs = unvault_emer_tx
        .inner_tx()
        .inputs
        .get(0)
        .expect("UnvaultEmergency tx has a single input, inbefore fee bumping.")
        .partial_sigs
        .clone();

    // Note that we are looping, but most (if not all) will only have a single signature
    // attached. We are called by the `revocationtxs` RPC, sent after a `getrevocationtxs`
    // which generates fresh unsigned transaction.

    // FIXME: use pop_last() once it's stable
    for (pubkey, sig) in cancel_sigs.into_iter() {
        let pubkey = pubkey.key;
        let signature = RevaultSignature::PlaintextSig(Signature::from_der(&sig)?);
        // TODO: check signature validity before sharing
        let id = cancel_tx.inner_tx().global.unsigned_tx.txid();
        let sig_msg = Sig {
            pubkey,
            signature,
            id,
        };
        // FIXME: here or upstream, we should retry until timeout
        transport.write(&serde_json::to_vec(&sig_msg)?)?;
    }

    // FIXME: use pop_last() once it's stable
    for (pubkey, sig) in emer_sigs.into_iter() {
        let pubkey = pubkey.key;
        let id = emer_tx.inner_tx().global.unsigned_tx.txid();
        for encryption_key in revaultd.sig_encryption_pubkeys.iter() {
            let encrypted_signature =
                encrypt_emergency_sig(&sig, &encryption_key, &revaultd.sig_encryption_secret);
            let signature = RevaultSignature::EncryptedSig {
                encryption_key: encryption_key.clone(),
                encrypted_signature,
            };
            let sig_msg = Sig {
                pubkey,
                signature,
                id,
            };
            // FIXME: here or upstream, we should retry until timeout
            transport.write(&serde_json::to_vec(&sig_msg)?)?;
        }
    }

    // FIXME: use pop_last() once it's stable
    for (pubkey, sig) in unvault_emer_sigs.into_iter() {
        let pubkey = pubkey.key;
        let id = unvault_emer_tx.inner_tx().global.unsigned_tx.txid();
        for encryption_key in revaultd.sig_encryption_pubkeys.iter() {
            let encrypted_signature =
                encrypt_emergency_sig(&sig, &encryption_key, &revaultd.sig_encryption_secret);
            let signature = RevaultSignature::EncryptedSig {
                encryption_key: encryption_key.clone(),
                encrypted_signature,
            };
            let sig_msg = Sig {
                pubkey,
                signature,
                id,
            };
            // FIXME: here or upstream, we should retry until timeout
            transport.write(&serde_json::to_vec(&sig_msg)?)?;
        }
    }

    Ok(())
}

// Will panic if called to fetch an Emergency signature for a Manager (ie no
// revaultd.sig_encryption_secret)
fn fetch_signatures(revaultd: Arc<RwLock<RevaultD>>, tx: impl RevaultTransaction) -> Result<impl RevaultTransaction, Box<dyn std::error::Error>> {
    let revaultd = revaultd.read().unwrap();
    let mut transport = KKTransport::connect(
        revaultd.coordinator_host,
        &revaultd.noise_secret,
        &revaultd.coordinator_noisekey,
    )?;
    let id = tx.inner_tx().global.unsigned_tx.txid();
    let getsigs_msg = GetSigs { id };

    loop {
        let got_new_sigs = false;

        let raw_msg = serde_json::to_vec(&getsigs_msg)?;
        log::trace!("Sending to sync server: '{}'", &String::from_utf8_lossy(&raw_msg));
        transport.write(&raw_msg)?;
        let recvd_raw = transport.read()?;
        log::trace!("Receiving from sync server: '{}'", &String::from_utf8_lossy(&recvd_raw));
        let Sigs { signatures } = serde_json::from_slice(&recvd_raw)?;

        for (key, sig) in signatures {
            let pubkey = BitcoinPubKey { compressed: true, key };
            if !tx.inner_tx().inputs[0].partial_sigs.contains_key(&pubkey) {
                log::debug!("Adding signature '{}' for pubkey '{}' for tx '{}'", sig, pubkey, id);
                match sig {
                    RevaultSignature::PlaintextSig(sig) => tx.add_signature(0, pubkey, sig)?,
                    RevaultSignature::EncryptedSig{ encryption_key, encrypted_signature } => {
                        let plaintext_sig = sodiumoxide
                    }
                }
                got_new_sigs = true;
            }
        }

        if got_new_sigs && tx.finalize(&revaultd.secp_ctx).is_ok() {
            log::debug!("Got all signatures for '{}'", id);
            return Ok(tx);
        }

        log::debug!("Still waiting for signatures for '{}'", id);
        std::thread::sleep(std::time::Duration::from_millis(500));
    }
}

/// Handle events incoming from the JSONRPC interface.
pub fn handle_rpc_messages(
    revaultd: Arc<RwLock<RevaultD>>,
    db_path: PathBuf,
    network: Network,
    rpc_rx: Receiver<RpcMessageIn>,
    bitcoind_tx: Sender<BitcoindMessageOut>,
    bitcoind_thread: JoinHandle<()>,
    jsonrpc_thread: JoinHandle<()>,
) -> Result<(), ControlError> {
    for msg in rpc_rx {
        match msg {
            RpcMessageIn::Shutdown => {
                log::info!("Stopping revaultd.");
                bitcoind_tx.send(BitcoindMessageOut::Shutdown)?;

                assume_ok!(jsonrpc_thread.join(), "Joining RPC server thread");
                assume_ok!(bitcoind_thread.join(), "Joining bitcoind thread");
                process::exit(0);
            }
            RpcMessageIn::GetInfo(response_tx) => {
                log::trace!("Got getinfo from RPC thread");

                let (bitrep_tx, bitrep_rx) = mpsc::sync_channel(0);
                bitcoind_tx.send(BitcoindMessageOut::SyncProgress(bitrep_tx))?;
                let progress = bitrep_rx.recv()?;

                // This means blockheight == 0 for IBD.
                let BlockchainTip {
                    height: blockheight,
                    ..
                } = db_tip(&db_path)?;

                response_tx.send((network.to_string(), blockheight, progress))?;
            }
            RpcMessageIn::ListVaults((statuses, outpoints), response_tx) => {
                log::trace!("Got listvaults from RPC thread");
                response_tx.send(listvaults_from_db(
                    &revaultd.read().unwrap(),
                    statuses,
                    outpoints,
                )?)?;
            }
            RpcMessageIn::DepositAddr(response_tx) => {
                log::trace!("Got 'depositaddr' request from RPC thread");
                response_tx.send(revaultd.read().unwrap().deposit_address())?;
            }
            RpcMessageIn::GetRevocationTxs(outpoint, response_tx) => {
                log::trace!("Got 'getrevocationtxs' request from RPC thread");
                let revaultd = revaultd.read().unwrap();
                let xpub_ctx = revaultd.xpub_ctx();
                let db_file = &revaultd.db_file();

                // First, make sure the vault exists and is confirmed.
                let vault = match db_vault_by_deposit(db_file, &outpoint)? {
                    None => None,
                    Some(vault) => match vault.status {
                        VaultStatus::Unconfirmed => None,
                        _ => Some(vault),
                    },
                };
                if let Some(vault) = vault {
                    // Second, derive the fully-specified deposit txout.
                    let deposit_descriptor =
                        revaultd.vault_descriptor.derive(vault.derivation_index);
                    let vault_txin = VaultTxIn::new(
                        outpoint,
                        VaultTxOut::new(vault.amount.as_sat(), &deposit_descriptor, xpub_ctx),
                    );

                    // Third, re-derive all the transactions out of it.
                    let unvault_descriptor =
                        revaultd.unvault_descriptor.derive(vault.derivation_index);
                    let cpfp_descriptor = revaultd.cpfp_descriptor.derive(vault.derivation_index);
                    let emer_address = revaultd.emergency_address.clone();

                    let (_, cancel, emergency, unvault_emer) = transaction_chain(
                        vault_txin,
                        &deposit_descriptor,
                        &unvault_descriptor,
                        &cpfp_descriptor,
                        emer_address,
                        xpub_ctx,
                        revaultd.lock_time,
                        revaultd.unvault_csv,
                    )?;

                    response_tx.send(Some((cancel, emergency, unvault_emer)))?;
                } else {
                    response_tx.send(None)?;
                }
            }
            RpcMessageIn::RevocationTxs(
                (outpoint, mut cancel, mut emer, mut unvault_emer),
                response_tx,
            ) => {
                log::trace!("Got 'revocationtxs' from RPC thread");
                let db_path = &revaultd.read().unwrap().db_file();

                // First, make sure the outpoint they are giving us transactions for actually
                // exists.
                let res = if let Some(db_vault) = db_vault_by_deposit(db_path, &outpoint)? {
                    // Then, start sharing signatures
                    let revaultd_share = revaultd.clone();
                    let (c, e, u) = (cancel.clone(), emer.clone(), unvault_emer.clone());
                    let sharing_thread = thread::spawn(move || {
                        if let Err(e) = share_signatures(revaultd_share, c, e, u) {
                            Some(e.to_string())
                        } else {
                            None
                        }
                    });

                    let 
                    if cancel.finalize(&revaultd.read().unwrap().secp_ctx).is_err() {
                        /* TODO: fetch from the SS */
                    }
                    if emer.finalize(&revaultd.read().unwrap().secp_ctx).is_err() {
                        /* TODO: fetch from the SS */
                    }
                    if unvault_emer
                        .finalize(&revaultd.read().unwrap().secp_ctx)
                        .is_err()
                    { /* TODO: fetch from the SS */ }

                    // TODO: unimplemented
                    if false {
                        db_store_revocation_txs(
                            &revaultd.read().unwrap().db_file(),
                            db_vault.id,
                            cancel,
                            emer,
                            unvault_emer,
                        )?;
                    }
                    None
                } else {
                    Some("Outpoint does not correspond to an existing vault".into())
                };

                let sharing_res = sharing_thread.join();

                response_tx.send(res)?;
            }
            RpcMessageIn::ListTransactions(outpoints, response_tx) => {
                log::trace!("Got 'listtransactions' request from RPC thread");
                response_tx.send(txlist_from_outpoints(
                    &revaultd.read().unwrap(),
                    &bitcoind_tx,
                    outpoints,
                )?)?;
            }
        }
    }

    Ok(())
}
