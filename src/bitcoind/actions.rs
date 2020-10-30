use crate::{
    bitcoind::{interface::BitcoinD, BitcoindError},
    config::BitcoindConfig,
    database::interface::{db_wallet, DbWallet},
    revaultd::RevaultD,
};

use std::{process, thread, time};

fn check_bitcoind_network(bitcoind: &BitcoinD, config_network: &str) -> Result<(), BitcoindError> {
    let chaininfo = bitcoind.getblockchaininfo()?;
    let chain = chaininfo
        .get("chain")
        .and_then(|c| c.as_str())
        .ok_or_else(|| {
            BitcoindError("No valid 'chain' in getblockchaininfo response?".to_owned())
        })?;

    if !config_network.eq(chain) {
        return Err(BitcoindError(format!(
            "Wrong network, bitcoind is on '{}' but our config says '{}'",
            chain, config_network
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

/// Polls bitcoind until we are synced.
/// Tries to be smart with getblockchaininfo calls.
fn wait_for_bitcoind_synced(
    bitcoind: &BitcoinD,
    bitcoind_config: &BitcoindConfig,
) -> Result<(), BitcoindError> {
    // We need to take the edge case in which all headers aren't downloaded yet
    // into account.
    let mut first = true;

    loop {
        let chaininfo = bitcoind.getblockchaininfo()?;
        let (headers, blocks, ibd) = (
            chaininfo
                .get("headers")
                .and_then(|h| h.as_u64())
                .ok_or_else(|| {
                    BitcoindError("No valid 'headers' in getblockchaininfo response?".to_owned())
                })?,
            chaininfo
                .get("blocks")
                .and_then(|b| b.as_u64())
                .ok_or_else(|| {
                    BitcoindError("No valid 'blocks' in getblockchaininfo response?".to_owned())
                })?,
            chaininfo
                .get("initialblockdownload")
                .and_then(|i| i.as_bool())
                .ok_or_else(|| {
                    BitcoindError(
                        "No valid 'initialblockdownload' in getblockchaininfo response?".to_owned(),
                    )
                })?,
        );
        let mut delta = if headers > blocks {
            headers - blocks
        } else {
            0
        };

        if ibd {
            // Ok, so we have some time. Let's try to avoid slowing it down by
            // spamming it with getblockchaininfo calls.

            if first {
                log::info!(
                    "Bitcoind is currently performing IBD, this is going to \
                        take some time."
                );
            }

            // First: wait for it to gather all headers, if the current delta is
            // big enough. let's assume it won't take longer than 5min from now
            // for mainnet.
            // Then: get the number of blocks left to DL
            if first || delta > 1_000 {
                log::info!("Waiting for bitcoind to gather enough headers..");
                if bitcoind_config.network.eq("regtest") {
                    thread::sleep(time::Duration::from_secs(3));
                } else {
                    thread::sleep(time::Duration::from_secs(5 * 60));
                }

                let chaininfo = bitcoind.getblockchaininfo()?;
                let (headers, blocks) = (
                    chaininfo
                        .get("headers")
                        .and_then(|h| h.as_u64())
                        .ok_or_else(|| {
                            BitcoindError(
                                "No valid 'headers' in getblockchaininfo response?".to_owned(),
                            )
                        })?,
                    chaininfo
                        .get("blocks")
                        .and_then(|b| b.as_u64())
                        .ok_or_else(|| {
                            BitcoindError(
                                "No valid 'blocks' in getblockchaininfo response?".to_owned(),
                            )
                        })?,
                );
                delta = headers - blocks;
            }
        } else if delta == 0 {
            return Ok(());
        }

        // Sleeping a second per 20 blocks seems a good upper bound estimation
        // (~7h for 500_000 blocks), so we divide it by 2 here in order to be
        // conservative. Eg if 10_000 are left to be downloaded we'll check back
        // in ~4min.
        let sleep_duration = time::Duration::from_secs(delta / 20 / 2);
        log::info!("We'll poll bitcoind again in {:?} seconds", sleep_duration);
        // FIXME: maybe Edouard will need more fine-grained updates eventually
        thread::sleep(sleep_duration);

        first = false;
    }
}

// This creates the actual wallet file, and imports the descriptors
fn maybe_create_wallet(revaultd: &RevaultD, bitcoind: &BitcoinD) -> Result<(), BitcoindError> {
    let wallet = db_wallet(&revaultd.db_file())
        .map_err(|e| BitcoindError(format!("Error getting wallet from db: {}", e.to_string())))?;
    let bitcoind_wallet_path = revaultd.watchonly_wallet_file(wallet.id);
    let bitcoind_wallet_str = bitcoind_wallet_path
        .to_str()
        .expect("Path is valid unicode")
        .to_string();

    if !bitcoind_wallet_path.exists() {
        bitcoind.createwallet_startup(bitcoind_wallet_str)?;

        // Now, import descriptors.
        // TODO: maybe warn, depending on the timestamp, that it's going to take some time.
        // In theory, we could just import the vault (deposit) descriptor expressed using xpubs, give a
        // range to bitcoind as the gap limit, and be fine.
        // Unfortunately we cannot just import descriptors as is, since bitcoind does not support
        // Miniscript ones yet. Worse, we actually need to derive them to pass them to bitcoind since
        // the vault one (which we are interested about) won't be expressed with a `multi()` statement (
        // currently supported by bitcoind) if there are more than 15 stakeholders.
        // Therefore, we derive [max index] `addr()` descriptors to import into bitcoind, and handle
        // the derivation index mess ourselves :'(
        let addresses = revaultd.all_deposit_addresses();
        let mut descriptors = Vec::<String>::with_capacity(addresses.len());
        for addr in addresses {
            descriptors.push(bitcoind.addr_descriptor(&addr)?);
        }
        log::trace!("Importing deposit descriptors '{:?}'", &descriptors);
        bitcoind.startup_importdescriptors(
            descriptors,
            wallet.timestamp,
            "revault-deposit".to_string(),
        )?;
    }

    Ok(())
}

fn maybe_load_wallet(revaultd: &RevaultD, bitcoind: &BitcoinD) -> Result<(), BitcoindError> {
    let wallet = db_wallet(&revaultd.db_file())
        .map_err(|e| BitcoindError(format!("Error getting wallet from db: {}", e.to_string())))?;
    let bitcoind_wallet_path = revaultd
        .watchonly_wallet_file(wallet.id)
        .to_str()
        .expect("Path is valid unicode")
        .to_string();

    if !bitcoind.listwallets()?.contains(&bitcoind_wallet_path) {
        log::info!("Loading wallet '{}'.", bitcoind_wallet_path);
        bitcoind.loadwallet_startup(bitcoind_wallet_path.clone())?;
    }

    for wallet_name in bitcoind.listwallets()? {
        if wallet_name != bitcoind_wallet_path {
            log::info!(
                "Too many wallets loaded on bitcoind! Unloading wallet '{}'.",
                wallet_name
            );
            bitcoind.unloadwallet(wallet_name)?;
        }
    }

    Ok(())
}

/// Connects to, sanity checks, and wait for bitcoind to be synced.
/// Called at startup, will log and abort on error.
pub fn setup_bitcoind(revaultd: &RevaultD) -> BitcoinD {
    let bitcoind = BitcoinD::new(&revaultd.bitcoind_config).unwrap_or_else(|e| {
        log::error!("Could not connect to bitcoind: {}", e.to_string());
        process::exit(1);
    });

    bitcoind_sanity_checks(&bitcoind, &revaultd.bitcoind_config).unwrap_or_else(|e| {
        // FIXME: handle warming up
        log::error!("Error checking bitcoind: {}", e.to_string());
        process::exit(1);
    });

    wait_for_bitcoind_synced(&bitcoind, &revaultd.bitcoind_config).unwrap_or_else(|e| {
        log::error!("Error while updating tip: {}", e.to_string());
        process::exit(1);
    });

    maybe_create_wallet(&revaultd, &bitcoind).unwrap_or_else(|e| {
        log::error!("Error while creating wallet: {}", e.to_string());
        process::exit(1);
    });
    maybe_load_wallet(&revaultd, &bitcoind).unwrap_or_else(|e| {
        log::error!("Error while loading wallet: {}", e.to_string());
        process::exit(1);
    });

    bitcoind
}
