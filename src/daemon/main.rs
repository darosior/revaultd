mod bitcoind;
mod database;
mod jsonrpc;
mod revaultd;
mod threadmessages;

use crate::{
    bitcoind::actions::{bitcoind_main_loop, start_bitcoind},
    database::{
        actions::setup_db,
        interface::{db_tip, db_transactions, db_vault_by_deposit, RevaultTx, TransactionType},
    },
    jsonrpc::{jsonrpcapi_loop, jsonrpcapi_setup},
    revaultd::{BlockchainTip, RevaultD, VaultStatus},
    threadmessages::*,
};
use common::config::Config;
use revault_tx::{transactions::transaction_chain, txins::VaultTxIn, txouts::VaultTxOut};

use std::{
    env,
    path::PathBuf,
    process,
    str::FromStr,
    sync::{mpsc, Arc, RwLock},
    thread,
};

use daemonize_simple::Daemonize;

fn parse_args(args: Vec<String>) -> Option<PathBuf> {
    if args.len() == 1 {
        return None;
    }

    if args.len() != 3 {
        eprintln!("Unknown arguments '{:?}'.", args);
        eprintln!("Only '--conf <configuration file path>' is supported.");
        process::exit(1);
    }

    Some(PathBuf::from(args[2].to_owned()))
}

fn daemon_main(mut revaultd: RevaultD) {
    let (db_path, network) = (revaultd.db_file(), revaultd.bitcoind_config.network);

    // First and foremost
    log::info!("Setting up database");
    setup_db(&mut revaultd).unwrap_or_else(|e| {
        log::error!("Error setting up database: '{}'", e.to_string());
        process::exit(1);
    });

    log::info!("Setting up bitcoind connection");
    let bitcoind = start_bitcoind(&mut revaultd).unwrap_or_else(|e| {
        log::error!("Error setting up bitcoind: {}", e.to_string());
        process::exit(1);
    });

    log::info!("Starting JSONRPC server");
    let socket = jsonrpcapi_setup(revaultd.rpc_socket_file()).unwrap_or_else(|e| {
        log::error!("Setting up JSONRPC server: {}", e.to_string());
        process::exit(1);
    });

    // We start two threads, the JSONRPC one in order to be controlled externally,
    // and the bitcoind one to poll bitcoind until we die.
    // We may get requests from the RPC one, and send requests to the bitcoind one.

    // The communication from them to us
    let (rpc_tx, rpc_rx) = mpsc::channel();

    // The communication from us to the bitcoind thread
    let (bitcoind_tx, bitcoind_rx) = mpsc::channel();

    let jsonrpc_thread = thread::spawn(move || {
        jsonrpcapi_loop(rpc_tx, socket).unwrap_or_else(|e| {
            log::error!("Error in JSONRPC server event loop: {}", e.to_string());
            process::exit(1)
        })
    });

    let revaultd = Arc::new(RwLock::new(revaultd));
    let bit_revaultd = revaultd.clone();
    let bitcoind_thread = thread::spawn(move || {
        bitcoind_main_loop(bitcoind_rx, bit_revaultd, &bitcoind).unwrap_or_else(|e| {
            log::error!("Error in bitcoind main loop: {}", e.to_string());
            process::exit(1)
        })
    });

    log::info!(
        "revaultd started on network {}",
        revaultd.read().unwrap().bitcoind_config.network
    );
    for message in rpc_rx {
        match message {
            RpcMessageIn::Shutdown => {
                log::info!("Stopping revaultd.");
                bitcoind_tx
                    .send(BitcoindMessageOut::Shutdown)
                    .unwrap_or_else(|e| {
                        log::error!("Sending shutdown to bitcoind thread: {:?}", e);
                        process::exit(1);
                    });

                jsonrpc_thread.join().unwrap_or_else(|e| {
                    log::error!("Joining RPC server thread: {:?}", e);
                    process::exit(1);
                });
                bitcoind_thread.join().unwrap_or_else(|e| {
                    log::error!("Joining bitcoind thread: {:?}", e);
                    process::exit(1);
                });
                process::exit(0);
            }
            RpcMessageIn::GetInfo(response_tx) => {
                log::trace!("Got getinfo from RPC thread");

                let (bitrep_tx, bitrep_rx) = mpsc::sync_channel(0);
                bitcoind_tx
                    .send(BitcoindMessageOut::SyncProgress(bitrep_tx))
                    .unwrap_or_else(|e| {
                        log::error!("Sending 'syncprogress' to bitcoind thread: {:?}", e);
                        process::exit(1);
                    });
                let progress = bitrep_rx.recv().unwrap_or_else(|e| {
                    log::error!("Receving 'syncprogress' from bitcoind thread: {:?}", e);
                    process::exit(1);
                });

                // This means blockheight == 0 for IBD.
                let BlockchainTip {
                    height: blockheight,
                    ..
                } = db_tip(&db_path).unwrap_or_else(|e| {
                    log::error!("Getting tip from db: {:?}", e);
                    process::exit(1);
                });

                response_tx
                    .send((network.to_string(), blockheight, progress))
                    // TODO: a macro for the unwrap_or_else boilerplate..
                    .unwrap_or_else(|e| {
                        log::error!("Sending 'getinfo' result to RPC thread: {:?}", e);
                        process::exit(1);
                    });
            }
            RpcMessageIn::ListVaults((statuses, outpoints), response_tx) => {
                log::trace!("Got listvaults from RPC thread");

                let mut resp = Vec::<(u64, String, String, u32)>::new();
                for (ref outpoint, ref vault) in revaultd.read().unwrap().vaults.iter() {
                    if let Some(ref statuses) = statuses {
                        if !statuses.contains(&vault.status) {
                            continue;
                        }
                    }

                    if let Some(ref outpoints) = &outpoints {
                        if !outpoints.contains(&outpoint) {
                            continue;
                        }
                    }

                    resp.push((
                        vault.txo.value,
                        vault.status.to_string(),
                        outpoint.txid.to_string(),
                        outpoint.vout,
                    ));
                }

                response_tx.send(resp).unwrap_or_else(|e| {
                    log::error!("Sending 'listvaults' result to RPC thread: {}", e);
                    process::exit(1);
                });
            }
            RpcMessageIn::DepositAddr(response_tx) => {
                log::trace!("Got 'depositaddr' request from RPC thread");
                response_tx
                    .send(revaultd.read().unwrap().deposit_address())
                    .unwrap_or_else(|e| {
                        log::error!("Sending 'depositaddr' result to RPC thread: {}", e);
                        process::exit(1);
                    });
            }
            RpcMessageIn::GetRevocationTxs(outpoint, response_tx) => {
                log::trace!("Got 'getrevocationtxs' request from RPC thread");
                let revaultd = revaultd.read().unwrap();
                let xpub_ctx = revaultd.xpub_ctx();

                // First, make sure the vault exists and is confirmed.
                let vault = match revaultd.vaults.get(&outpoint) {
                    None => None,
                    Some(vault) => match vault.status {
                        VaultStatus::Unconfirmed => None,
                        _ => Some(vault),
                    },
                };
                if let Some(vault) = vault {
                    // Second, derive the fully-specified deposit txout. Note that we'd probably
                    // store the index in the cache eventually, but until we get rid of this awful
                    // mapping let's just use it.
                    let index = revaultd
                        .derivation_index_map
                        .get(&vault.txo.script_pubkey)
                        .unwrap_or_else(|| {
                            log::error!("Unknown derivation index for: {:#?}", vault);
                            process::exit(1);
                        });
                    let deposit_descriptor = revaultd.vault_descriptor.derive(*index);
                    let vault_txin = VaultTxIn::new(
                        outpoint,
                        VaultTxOut::new(vault.txo.value, &deposit_descriptor, xpub_ctx),
                    );

                    // Third, re-derive all the transactions out of it.
                    let unvault_descriptor = revaultd.unvault_descriptor.derive(*index);
                    let cpfp_descriptor = revaultd.cpfp_descriptor.derive(*index);
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
                    )
                    .unwrap_or_else(|e| {
                        log::error!(
                            "Deriving transactions for vault {:#?} (at '{}'): '{}'",
                            vault,
                            outpoint,
                            e
                        );
                        process::exit(1);
                    });

                    response_tx
                        .send(Some((cancel, emergency, unvault_emer)))
                        .unwrap_or_else(|e| {
                            log::error!("Sending 'getrevocationtxs' result to RPC thread: '{}'", e);
                            process::exit(1);
                        });
                } else {
                    response_tx.send(None).unwrap_or_else(|e| {
                        log::error!(
                            "Sending 'getrevocationtxs' (None) result to RPC thread: '{}'",
                            e
                        );
                        process::exit(1);
                    });
                }
            }
            RpcMessageIn::GetOnchainTxs(outpoint, response_tx) => {
                log::trace!("Got 'getonchaintxs' request from RPC thread");
                let revaultd = revaultd.read().unwrap();

                // First, make sure the vault exists and is confirmed.
                if let Some(vault) = revaultd.vaults.get(&outpoint) {
                    let db_vault = db_vault_by_deposit(&db_path, &outpoint)
                        .unwrap_or_else(|e| {
                            log::error!("Getting vault from db: {}", e);
                            process::exit(1);
                        })
                        .unwrap_or_else(|| {
                            log::error!("(Insane db) None vault for '{}'", &outpoint);
                            process::exit(1);
                        });

                    let onchain_txs = match vault.status {
                        // No onchain transaction yet
                        VaultStatus::Unconfirmed
                        | VaultStatus::Funded
                        | VaultStatus::Secured
                        | VaultStatus::Active
                        | VaultStatus::Unvaulting
                        | VaultStatus::EmergencyVaulting => (None, None, None, None, None),
                        // Only the unvault is confirmed at this point
                        VaultStatus::Unvaulted
                        | VaultStatus::Canceling
                        | VaultStatus::Spendable
                        | VaultStatus::Spending
                        | VaultStatus::UnvaultEmergencyVaulting => {
                            let tx =
                                db_transactions(&db_path, db_vault.id, &[TransactionType::Unvault])
                                    .unwrap_or_else(|e| {
                                        log::error!(
                                            "Getting transactions (unvault) from db: {}",
                                            e
                                        );
                                        process::exit(1);
                                    })
                                    .pop()
                                    .unwrap_or_else(|| {
                                        log::error!(
                                            "No Unvault tx in db for vault at {} (status: {})",
                                            outpoint,
                                            vault.status
                                        );
                                        process::exit(1);
                                    })
                                    .tx;
                            let unvault_tx = assert_tx_type!(
                                tx,
                                Unvault,
                                "db_transactions() was given TransactionType::Unvault"
                            );

                            (Some(unvault_tx), None, None, None, None)
                        }
                        // Both the spend and the unvault are here
                        VaultStatus::Spent => {
                            let mut txs = db_transactions(
                                &db_path,
                                db_vault.id,
                                &[TransactionType::Unvault, TransactionType::Spend],
                            )
                            .unwrap_or_else(|e| {
                                log::error!("Getting transactions (unvault, spend) from db: {}", e);
                                process::exit(1);
                            });
                            if txs.len() != 2 {
                                log::error!(
                                    "invalid db_transactions() result for Spent vault: {:#?}",
                                    txs
                                );
                                process::exit(1);
                            }

                            // We can't assume the ordering, so we support both..
                            match txs.pop().unwrap().tx {
                                RevaultTx::Unvault(unvault_tx) => {
                                    let spend_tx = assert_tx_type!(
                                        txs.pop().unwrap().tx,
                                        Spend,
                                        "Unvault and Spend passed to db_transactions"
                                    );
                                    (Some(unvault_tx), Some(spend_tx), None, None, None)
                                }
                                RevaultTx::Spend(spend_tx) => {
                                    let unvault_tx = assert_tx_type!(
                                        txs.pop().unwrap().tx,
                                        Unvault,
                                        "Unvault and Spend passed to db_transactions"
                                    );
                                    (Some(unvault_tx), Some(spend_tx), None, None, None)
                                }
                                _ => unreachable!("Unvault and Spend passed to db_transactions"),
                            }
                        }
                        // Both the unvault and the cancel are here
                        VaultStatus::Canceled => {
                            let mut txs = db_transactions(
                                &db_path,
                                db_vault.id,
                                &[TransactionType::Unvault, TransactionType::Cancel],
                            )
                            .unwrap_or_else(|e| {
                                log::error!(
                                    "Getting transactions (unvault, cancel) from db: {}",
                                    e
                                );
                                process::exit(1);
                            });
                            if txs.len() != 2 {
                                log::error!(
                                    "invalid db_transactions() result for Canceled vault: {:#?}",
                                    txs
                                );
                                process::exit(1);
                            }

                            // We can't assume the ordering, so we support both..
                            match txs.pop().unwrap().tx {
                                RevaultTx::Unvault(unvault_tx) => {
                                    let cancel_tx = assert_tx_type!(
                                        txs.pop().unwrap().tx,
                                        Cancel,
                                        "Unvault and Cancel passed to db_transactions"
                                    );
                                    (Some(unvault_tx), None, Some(cancel_tx), None, None)
                                }
                                RevaultTx::Cancel(cancel_tx) => {
                                    let unvault_tx = assert_tx_type!(
                                        txs.pop().unwrap().tx,
                                        Unvault,
                                        "Unvault and Cancel passed to db_transactions"
                                    );
                                    (Some(unvault_tx), None, Some(cancel_tx), None, None)
                                }
                                _ => unreachable!("Unvault and Spend passed to db_transactions"),
                            }
                        }
                        // Only the first Emergency is confirmed
                        VaultStatus::EmergencyVaulted => {
                            let tx = db_transactions(
                                &db_path,
                                db_vault.id,
                                &[TransactionType::Emergency],
                            )
                            .unwrap_or_else(|e| {
                                log::error!("Getting transactions (emergency) from db: {}", e);
                                process::exit(1);
                            })
                            .pop()
                            .unwrap_or_else(|| {
                                log::error!(
                                    "No Emergency tx in db for vault at {} (status: {})",
                                    outpoint,
                                    vault.status
                                );
                                process::exit(1);
                            })
                            .tx;
                            let emer_tx = assert_tx_type!(
                                tx,
                                Emergency,
                                "db_transactions() was given TransactionType::Emergency"
                            );

                            (None, None, None, Some(emer_tx), None)
                        }
                        // Both the unvault and the cancel are here
                        VaultStatus::UnvaultEmergencyVaulted => {
                            let mut txs = db_transactions(
                                &db_path,
                                db_vault.id,
                                &[TransactionType::Unvault, TransactionType::UnvaultEmergency],
                            )
                            .unwrap_or_else(|e| {
                                log::error!(
                                    "Getting transactions (unvault, emergency) from db: {}",
                                    e
                                );
                                process::exit(1);
                            })
                            .into_iter();

                            let unvault_tx = txs
                                .find(|db_tx| matches!(db_tx.tx, RevaultTx::Unvault(_)))
                                .unwrap_or_else(|| {
                                    log::error!(
                                        "Vault in UnvaultEmergencyVaulted state but no Unvault tx in db",
                                    );
                                    process::exit(1);
                                });
                            let unvault_tx =
                                assert_tx_type!(unvault_tx.tx, Unvault, "We just found it");

                            let unemer_tx = txs
                                .find(|db_tx| matches!(db_tx.tx, RevaultTx::UnvaultEmergency(_)))
                                .unwrap_or_else(|| {
                                    log::error!(
                                        "Vault in UnvaultEmergencyVaulted state but no UnvaultEmergency tx in db",
                                    );
                                    process::exit(1);
                                });
                            let unemer_tx =
                                assert_tx_type!(unemer_tx.tx, UnvaultEmergency, "We just found it");

                            (Some(unvault_tx), None, None, None, Some(unemer_tx))
                        }
                    };

                    response_tx.send(onchain_txs).unwrap_or_else(|e| {
                        log::error!("Sending 'getonchaintxs' result to RPC thread: {}", e);
                        process::exit(1);
                    });
                }
            }
        }
    }
}

// This creates the log file automagically if it doesn't exist, and logs on stdout
// if None is given
fn setup_logger(
    log_file: Option<&str>,
    log_level: log::LevelFilter,
) -> Result<(), fern::InitError> {
    let dispatcher = fern::Dispatch::new()
        .format(|out, message, record| {
            out.finish(format_args!(
                "{}[{}][{}] {}",
                chrono::Local::now().format("[%Y-%m-%d][%H:%M:%S]"),
                record.target(),
                record.level(),
                message
            ))
        })
        .level(log_level);

    if let Some(log_file) = log_file {
        dispatcher.chain(fern::log_file(log_file)?).apply()?;
    } else {
        dispatcher.chain(std::io::stdout()).apply()?;
    }

    Ok(())
}

fn main() {
    let args = env::args().collect();
    let conf_file = parse_args(args);

    let config = Config::from_file(conf_file).unwrap_or_else(|e| {
        eprintln!("Error parsing config: {}", e);
        process::exit(1);
    });
    let log_level = if let Some(ref level) = &config.log_level {
        log::LevelFilter::from_str(level.as_str()).unwrap_or_else(|e| {
            eprintln!("Invalid log level: {}", e);
            process::exit(1);
        })
    } else {
        log::LevelFilter::Info
    };
    // FIXME: should probably be from_db(), would allow us to not use Option members
    let revaultd = RevaultD::from_config(config).unwrap_or_else(|e| {
        eprintln!("Error creating global state: {}", e);
        process::exit(1);
    });

    let log_file = revaultd.log_file();
    let log_output = if revaultd.daemon {
        Some(log_file.to_str().expect("Valid unicode"))
    } else {
        None
    };
    setup_logger(log_output, log_level).unwrap_or_else(|e| {
        eprintln!("Error setting up logger: {}", e);
        process::exit(1);
    });

    if revaultd.daemon {
        let daemon = Daemonize {
            // TODO: Make this configurable for inits
            pid_file: Some(revaultd.pid_file()),
            ..Daemonize::default()
        };
        daemon.doit().unwrap_or_else(|e| {
            eprintln!("Error daemonizing: {}", e);
            process::exit(1);
        });
        println!("Started revaultd daemon");
    }

    daemon_main(revaultd);
}
