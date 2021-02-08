use crate::{
    bitcoind::{
        interface::{BitcoinD, DepositInfo, SyncInfo},
        BitcoindError,
    },
    database::{
        actions::{
            db_confirm_deposit, db_insert_new_unconfirmed_vault, db_unvault_deposit,
            db_update_deposit_index, db_update_tip,
        },
        interface::{db_deposits, db_wallet},
    },
    revaultd::{RevaultD, VaultStatus},
    threadmessages::{BitcoindMessageOut, WalletTransaction},
};
use common::config::BitcoindConfig;
use revault_tx::bitcoin::{Amount, Network, OutPoint, TxOut, Txid};

use std::{
    collections::HashMap,
    path::PathBuf,
    sync::{
        mpsc::{Receiver, TryRecvError},
        Arc, RwLock,
    },
    thread,
    time::{Duration, Instant, SystemTime, UNIX_EPOCH},
};

fn check_bitcoind_network(
    bitcoind: &BitcoinD,
    config_network: &Network,
) -> Result<(), BitcoindError> {
    let chaininfo = bitcoind.getblockchaininfo()?;
    let chain = chaininfo
        .get("chain")
        .and_then(|c| c.as_str())
        .ok_or_else(|| {
            BitcoindError::Custom("No valid 'chain' in getblockchaininfo response?".to_owned())
        })?;
    let bip70_net = match config_network {
        Network::Bitcoin => "main",
        Network::Testnet => "test",
        Network::Regtest => "regtest",
    };

    if !bip70_net.eq(chain) {
        return Err(BitcoindError::Custom(format!(
            "Wrong network, bitcoind is on '{}' but our config says '{}' ({})",
            chain, bip70_net, config_network
        )));
    }

    Ok(())
}

/// Some sanity checks to be done at startup to make sure our bitcoind isn't going to fail under
/// our feet for a legitimate reason.
fn bitcoind_sanity_checks(
    bitcoind: &BitcoinD,
    bitcoind_config: &BitcoindConfig,
) -> Result<(), BitcoindError> {
    check_bitcoind_network(&bitcoind, &bitcoind_config.network)
}

/// Bitcoind uses a guess for the value of verificationprogress. It will eventually get to
/// be 1, but can take some time; when it's > 0.99999 we are synced anyways so use that.
fn roundup_progress(progress: f64) -> f64 {
    let precision = 10u64.pow(5);
    ((progress * precision as f64 + 1.0) as u64 / precision) as f64
}

/// Polls bitcoind to check if we are synced yet.
/// Tries to be smart with getblockchaininfo calls by adjsuting the sleep duration
/// between calls.
/// If sync_progress == 1.0, we are done.
fn bitcoind_sync_status(
    bitcoind: &BitcoinD,
    bitcoind_config: &BitcoindConfig,
    sleep_duration: &mut Option<Duration>,
    sync_progress: &mut f64,
) -> Result<(), BitcoindError> {
    let first_poll = sleep_duration.is_none();

    let SyncInfo {
        headers,
        blocks,
        ibd,
        progress,
    } = bitcoind.synchronization_info()?;
    *sync_progress = roundup_progress(progress);

    if first_poll {
        if ibd {
            log::info!(
                "Bitcoind is currently performing IBD, this is going to \
                        take some time."
            );

            // If it may not have received all headers, be conservative and wait
            // for that first. Let's assume it won't take longer than 5min from now
            // for mainnet.
            if progress < 0.01 {
                log::info!("Waiting for bitcoind to gather enough headers..");

                *sleep_duration = if bitcoind_config.network.to_string().eq("regtest") {
                    Some(Duration::from_secs(3))
                } else {
                    Some(Duration::from_secs(5 * 60))
                };

                return Ok(());
            }
        }

        if progress < 0.7 {
            log::info!(
                "Bitcoind is far behind network tip, this is going to \
                        take some time."
            );
        }
    }

    // Sleeping a second per 20 blocks seems a good upper bound estimation
    // (~7h for 500_000 blocks), so we divide it by 2 here in order to be
    // conservative. Eg if 10_000 are left to be downloaded we'll check back
    // in ~4min.
    let delta = if headers > blocks {
        headers - blocks
    } else {
        0
    };
    *sleep_duration = Some(std::cmp::max(
        Duration::from_secs(delta / 20 / 2),
        Duration::from_secs(5),
    ));

    log::info!("We'll poll bitcoind again in {:?} seconds", sleep_duration);

    Ok(())
}

// This creates the actual wallet file, and imports the descriptors
fn maybe_create_wallet(revaultd: &mut RevaultD, bitcoind: &BitcoinD) -> Result<(), BitcoindError> {
    let wallet = db_wallet(&revaultd.db_file())?;
    let bitcoind_wallet_path = revaultd
        .watchonly_wallet_file()
        .expect("Wallet id is set at startup in setup_db()");
    // Did we just create the wallet ?
    let curr_timestamp = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|dur| dur.as_secs())
        .map_err(|e| {
            BitcoindError::Custom(format!("Computing time since epoch: {}", e.to_string()))
        })?;
    let fresh_wallet = (curr_timestamp - wallet.timestamp as u64) < 30;

    if !PathBuf::from(bitcoind_wallet_path.clone()).exists() {
        bitcoind.createwallet_startup(bitcoind_wallet_path)?;
        log::info!("Importing descriptors to bitcoind watchonly wallet.");

        // Now, import descriptors.
        // In theory, we could just import the vault (deposit) descriptor expressed using xpubs, give a
        // range to bitcoind as the gap limit, and be fine.
        // Unfortunately we cannot just import descriptors as is, since bitcoind does not support
        // Miniscript ones yet. Worse, we actually need to derive them to pass them to bitcoind since
        // the vault one (which we are interested about) won't be expressed with a `multi()` statement (
        // currently supported by bitcoind) if there are more than 15 stakeholders.
        // Therefore, we derive [max index] `addr()` descriptors to import into bitcoind, and handle
        // the derivation index mess ourselves :'(
        let mut addresses = revaultd.all_deposit_addresses();
        for i in 0..addresses.len() {
            addresses[i] = bitcoind.addr_descriptor(&addresses[i])?;
        }
        log::trace!("Importing deposit descriptors '{:?}'", &addresses);
        bitcoind.startup_import_deposit_descriptors(addresses, wallet.timestamp, fresh_wallet)?;

        // As a consequence, we don't have enough information to opportunistically import a
        // descriptor at the reception of a deposit anymore. Thus we need to blindly import *both*
        // deposit and unvault descriptors..
        // FIXME: maybe we actually have, with the derivation_index_map ?
        let mut addresses = revaultd.all_unvault_addresses();
        for i in 0..addresses.len() {
            addresses[i] = bitcoind.addr_descriptor(&addresses[i])?;
        }
        log::trace!("Importing unvault descriptors '{:?}'", &addresses);
        bitcoind.startup_import_unvault_descriptors(addresses, wallet.timestamp, fresh_wallet)?;
    }

    Ok(())
}

fn maybe_load_wallet(revaultd: &RevaultD, bitcoind: &BitcoinD) -> Result<(), BitcoindError> {
    let bitcoind_wallet_path = revaultd
        .watchonly_wallet_file()
        .expect("Wallet id is set at startup in setup_db()");

    if !bitcoind.listwallets()?.contains(&bitcoind_wallet_path) {
        log::info!("Loading our watchonly wallet '{}'.", bitcoind_wallet_path);
        bitcoind.loadwallet_startup(bitcoind_wallet_path)?;
    }

    Ok(())
}

/// Connects to and sanity checks bitcoind.
pub fn start_bitcoind(revaultd: &mut RevaultD) -> Result<BitcoinD, BitcoindError> {
    let bitcoind = BitcoinD::new(
        &revaultd.bitcoind_config,
        revaultd
            .watchonly_wallet_file()
            .expect("Wallet id is set at startup in setup_db()"),
    )
    .map_err(|e| {
        BitcoindError::Custom(format!("Could not connect to bitcoind: {}", e.to_string()))
    })?;

    while let Err(e) = bitcoind_sanity_checks(&bitcoind, &revaultd.bitcoind_config) {
        if e.is_warming_up() {
            log::info!("Bitcoind is warming up. Waiting for it to be back up.");
            thread::sleep(Duration::from_secs(3))
        } else {
            return Err(e);
        }
    }

    Ok(bitcoind)
}

fn update_tip(
    revaultd: &mut Arc<RwLock<RevaultD>>,
    bitcoind: &BitcoinD,
) -> Result<(), BitcoindError> {
    let tip = bitcoind.get_tip()?;
    let current_tip = revaultd.read().unwrap().tip.expect("Set at startup..");

    if tip != current_tip {
        db_update_tip(&revaultd.read().unwrap().db_file(), tip)?;
        revaultd.write().unwrap().tip = Some(tip);

        log::debug!("New tip: {:#?}", &tip);
    }

    Ok(())
}

// Fill up the deposit UTXOs cache from db vaults
fn populate_deposit_cache(
    revaultd: &RevaultD,
) -> Result<HashMap<OutPoint, DepositInfo>, BitcoindError> {
    let db_vaults = db_deposits(&revaultd.db_file())?;
    let mut cache = HashMap::with_capacity(db_vaults.len());

    for db_vault in db_vaults.into_iter() {
        let script_pubkey = revaultd
            .vault_address(db_vault.derivation_index)
            .script_pubkey();
        let txo = TxOut {
            script_pubkey,
            value: db_vault.amount.as_sat(),
        };
        cache.insert(
            db_vault.deposit_outpoint,
            DepositInfo {
                txo,
                status: db_vault.status,
            },
        );
        log::trace!("Loaded deposit '{}' from db", db_vault.deposit_outpoint);
    }

    Ok(cache)
}

// This syncs with bitcoind our incoming deposits, and those that were spent.
fn update_deposits(
    revaultd: &mut Arc<RwLock<RevaultD>>,
    bitcoind: &BitcoinD,
    deposits_cache: &mut HashMap<OutPoint, DepositInfo>,
) -> Result<(), BitcoindError> {
    // Sync deposit of vaults we know have an unspent deposit.
    let (new_deposits, conf_deposits, spent_deposits) = bitcoind.sync_deposits(&deposits_cache)?;

    for (outpoint, utxo) in new_deposits.into_iter() {
        let derivation_index = *revaultd
            .read()
            .unwrap()
            .derivation_index_map
            .get(&utxo.txo.script_pubkey)
            .ok_or_else(|| {
                BitcoindError::Custom(format!("Unknown derivation index for: {:#?}", &utxo))
            })?;

        // Note that the deposit *might* have already MIN_CONF confirmations, that's fine. We'll
        // confim it during the next poll.
        let amount = Amount::from_sat(utxo.txo.value);
        db_insert_new_unconfirmed_vault(
            &revaultd.read().unwrap().db_file(),
            revaultd
                .read()
                .unwrap()
                .wallet_id
                .expect("Wallet id is set at startup in setup_db()"),
            &utxo.status,
            &outpoint,
            &amount,
            derivation_index,
        )?;
        log::debug!(
            "Got a new unconfirmed deposit at {} for {} ({})",
            &outpoint,
            &utxo.txo.script_pubkey,
            &amount
        );
        deposits_cache.insert(outpoint, utxo);

        // Mind the gap! https://www.youtube.com/watch?v=UOPyGKDQuRk
        // FIXME: of course, that's rudimentary
        let current_first_index = revaultd.read().unwrap().current_unused_index;
        if derivation_index >= current_first_index {
            let new_index = revaultd
                .read()
                .unwrap()
                .current_unused_index
                .increment()
                .map_err(|e| {
                    // FIXME: we should probably go back to 0 at this point.
                    BitcoindError::Custom(format!("Deriving next index: {}", e))
                })?;
            db_update_deposit_index(&revaultd.read().unwrap().db_file(), new_index)?;
            revaultd.write().unwrap().current_unused_index = new_index;
            let next_addr = bitcoind
                .addr_descriptor(&revaultd.read().unwrap().last_deposit_address().to_string())?;
            bitcoind.import_fresh_deposit_descriptor(next_addr)?;
            let next_addr = bitcoind
                .addr_descriptor(&revaultd.read().unwrap().last_unvault_address().to_string())?;
            bitcoind.import_fresh_unvault_descriptor(next_addr)?;

            log::debug!(
                "Incremented deposit derivation index from {}",
                current_first_index
            );
        }
    }

    for (outpoint, _) in conf_deposits.into_iter() {
        let blockheight = bitcoind
            .get_wallet_transaction(outpoint.txid)?
            .1
            .ok_or_else(|| {
                BitcoindError::Custom("Deposit transaction isn't confirmed!".to_string())
            })?;
        db_confirm_deposit(&revaultd.read().unwrap().db_file(), &outpoint, blockheight)?;
        deposits_cache
            .get_mut(&outpoint)
            .ok_or_else(|| BitcoindError::Custom("An unknown vault got confirmed?".to_string()))?
            .status = VaultStatus::Funded;

        log::debug!("Vault at {} is now confirmed", &outpoint);
    }

    for (outpoint, utxo) in spent_deposits.into_iter() {
        let deriv_index = *revaultd.read().unwrap()
            .derivation_index_map
            .get(&utxo.txo.script_pubkey)
            .ok_or_else(|| BitcoindError::Custom(
                    format!("A deposit was spent for which we don't know the corresponding xpub derivation. Outpoint: '{}'\nUtxo: '{:#?}'",
                        &outpoint,
                        &utxo)))?;
        let unvault_addr = revaultd
            .read()
            .unwrap()
            .unvault_address(deriv_index)
            .to_string();

        if let Some(unvault_outpoint) = bitcoind.unvault_from_vault(&outpoint, unvault_addr)? {
            // Note that it *might* have actually been confirmed during the last 30s, but it's not
            // a big deal to have it marked as unconfirmed for the next 30s..
            db_unvault_deposit(&revaultd.read().unwrap().db_file(), &outpoint)?;
            deposits_cache
                .get_mut(&outpoint)
                .expect("We just checked it")
                .status = VaultStatus::Unvaulting;
            log::debug!(
                "The deposit utxo created via '{}' was unvaulted via '{}'",
                &outpoint,
                &unvault_outpoint
            );
        } else if false {
            // TODO: handle bypass and emergency
        } else {
            match utxo.status {
                // Fine.
                VaultStatus::Unconfirmed => log::debug!(
                    "The unconfirmed deposit utxo created via '{}' just vanished",
                    &outpoint
                ),
                // Bad.
                VaultStatus::Funded | VaultStatus::Secured => log::warn!(
                    "The deposit utxo created via '{}' just vanished. Maybe a reorg is ongoing?",
                    &outpoint
                ),
                // Impossible.
                _ => unreachable!(),
            }
        }
    }

    // TODO: keep track of unconfirmed unvaults and eventually mark them as confirmed

    Ok(())
}

fn wallet_transaction(bitcoind: &BitcoinD, txid: Txid) -> Option<WalletTransaction> {
    let res = bitcoind.get_wallet_transaction(txid);
    if let Ok((hex, blockheight, received_time)) = res {
        Some(WalletTransaction {
            hex,
            blockheight,
            received_time,
        })
    } else {
        log::trace!(
            "Got '{:?}' from bitcoind when requesting wallet transaction '{}'",
            res,
            txid
        );
        None
    }
}

/// The bitcoind event loop.
/// Poll bitcoind every 30 seconds, and update our state accordingly.
pub fn bitcoind_main_loop(
    rx: Receiver<BitcoindMessageOut>,
    mut revaultd: Arc<RwLock<RevaultD>>,
    bitcoind: &BitcoinD,
) -> Result<(), BitcoindError> {
    let mut last_poll = None;
    let mut sync_waittime = None;
    // The verification progress announced by bitcoind *at startup* thus won't be updated
    // after startup check. Should be *exactly* 1.0 when synced, but hey, floats so we are
    // careful.
    let mut sync_progress = 0.0f64;
    // When bitcoind is synced, we poll each 30s. On regtest we speed it up for testing.
    let poll_interval = match revaultd.read().unwrap().bitcoind_config.network {
        Network::Regtest => Duration::from_secs(3),
        _ => Duration::from_secs(30),
    };
    // We use a cache for maintaining our deposits' state up-to-date by polling `listunspent`
    let mut deposits_cache = populate_deposit_cache(&revaultd.read().unwrap())?;

    loop {
        let now = Instant::now();

        // If master told us something to do, do it now.
        match rx.try_recv() {
            Ok(msg) => match msg {
                BitcoindMessageOut::Shutdown => {
                    log::info!("Bitcoind received shutdown from main. Exiting.");
                    return Ok(());
                }
                BitcoindMessageOut::SyncProgress(resp_tx) => {
                    resp_tx.send(sync_progress).map_err(|e| {
                        BitcoindError::Custom(format!(
                            "Sending synchronization progress to main thread: {}",
                            e
                        ))
                    })?;
                }
                BitcoindMessageOut::WalletTransaction(txid, resp_tx) => {
                    log::trace!("Received 'wallettransaction' from main thread");
                    resp_tx
                        .send(wallet_transaction(&bitcoind, txid))
                        .map_err(|e| {
                            BitcoindError::Custom(format!(
                                "Sending wallet transaction to main thread: {}",
                                e
                            ))
                        })?;
                }
            },
            Err(TryRecvError::Empty) => {}
            Err(TryRecvError::Disconnected) => {
                log::error!("Channel with main thread disconnected. Exiting.");
                return Err(BitcoindError::Custom("Channel disconnected".to_string()));
            }
        };

        if (sync_progress as u32) < 1 {
            // While waiting for bitcoind to be synced, guesstimate how much time of block
            // connection we have left to not harass it with `getblockchaininfo`.
            if let Some(last) = last_poll {
                if let Some(waittime) = sync_waittime {
                    if now.duration_since(last) < waittime {
                        continue;
                    }
                }
            }

            bitcoind_sync_status(
                &bitcoind,
                &revaultd.read().unwrap().bitcoind_config,
                &mut sync_waittime,
                &mut sync_progress,
            )?;

            // Ok. Sync, done. Now just be sure the watchonly wallet is properly loaded, and
            // to create it if it's first run.
            if sync_progress as u32 >= 1 {
                let mut revaultd = revaultd.write().unwrap();
                maybe_create_wallet(&mut revaultd, &bitcoind).map_err(|e| {
                    BitcoindError::Custom(format!("Error while creating wallet: {}", e.to_string()))
                })?;
                maybe_load_wallet(&revaultd, &bitcoind).map_err(|e| {
                    BitcoindError::Custom(format!("Error while loading wallet: {}", e.to_string()))
                })?;

                log::info!("bitcoind now synced.");
            }

            last_poll = Some(now);
            continue;
        }

        // When bitcoind isn't synced, poll each 30s
        if let Some(last_poll) = last_poll {
            if now.duration_since(last_poll) < poll_interval {
                thread::sleep(poll_interval - now.duration_since(last_poll));
                continue;
            }
        }

        last_poll = Some(now);
        update_deposits(&mut revaultd, &bitcoind, &mut deposits_cache)?;
        update_tip(&mut revaultd, &bitcoind)?;
    }
}
