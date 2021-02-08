use crate::{
    bitcoind::{BitcoindError, MIN_CONF},
    revaultd::{BlockchainTip, VaultStatus},
};
use common::config::BitcoindConfig;
use revault_tx::bitcoin::{Address, Amount, BlockHash, OutPoint, TxOut, Txid};

use std::{collections::HashMap, fs, str::FromStr, time::Duration};

use jsonrpc::{arg, client::Client, simple_http::SimpleHttpTransport};
use serde_json::Value as Json;

pub struct BitcoinD {
    node_client: Client,
    watchonly_client: Client,
}

macro_rules! params {
    ($($param:expr),* $(,)?) => {
        [
            $(
                arg($param),
            )*
        ]
    };
}

impl BitcoinD {
    pub fn new(
        config: &BitcoindConfig,
        watchonly_wallet_path: String,
    ) -> Result<BitcoinD, BitcoindError> {
        let cookie_string = fs::read_to_string(&config.cookie_path).map_err(|e| {
            BitcoindError::Custom(format!("Reading cookie file: {}", e.to_string()))
        })?;

        let node_client = Client::with_transport(
            SimpleHttpTransport::builder()
                .url(&config.addr.to_string())
                .map_err(BitcoindError::from)?
                .timeout(Duration::from_secs(30))
                .cookie_auth(cookie_string.clone())
                .build(),
        );

        let url = format!("http://{}/wallet/{}", config.addr, watchonly_wallet_path);
        let watchonly_client = Client::with_transport(
            SimpleHttpTransport::builder()
                .url(&url)
                .map_err(BitcoindError::from)?
                .timeout(Duration::from_secs(30))
                .cookie_auth(cookie_string)
                .build(),
        );

        Ok(BitcoinD {
            node_client,
            watchonly_client,
        })
    }

    fn deposit_utxos_label(&self) -> String {
        "revault-deposit".to_string()
    }

    fn unvault_utxos_label(&self) -> String {
        "revault-unvault".to_string()
    }

    fn make_request<'a, 'b>(
        &self,
        client: &Client,
        method: &'a str,
        params: &'b [Box<serde_json::value::RawValue>],
    ) -> Result<Json, BitcoindError> {
        let req = client.build_request(method, &params);
        log::trace!("Sending to bitcoind: {:#?}", req);
        let resp = client.send_request(req).map_err(BitcoindError::Server)?;
        let res = resp.result().map_err(BitcoindError::Server)?;
        log::trace!("Got from bitcoind: {:#?}", res);

        Ok(res)
    }

    fn make_node_request<'a, 'b>(
        &self,
        method: &'a str,
        params: &'b [Box<serde_json::value::RawValue>],
    ) -> Result<Json, BitcoindError> {
        self.make_request(&self.node_client, method, params)
    }

    fn make_watchonly_request<'a, 'b>(
        &self,
        method: &'a str,
        params: &'b [Box<serde_json::value::RawValue>],
    ) -> Result<Json, BitcoindError> {
        self.make_request(&self.watchonly_client, method, params)
    }

    pub fn getblockchaininfo(&self) -> Result<Json, BitcoindError> {
        self.make_node_request("getblockchaininfo", &[])
    }

    pub fn get_tip(&self) -> Result<BlockchainTip, BitcoindError> {
        let json_height = self.make_node_request("getblockcount", &[])?;
        let height = json_height.as_u64().ok_or_else(|| {
            BitcoindError::Custom("API break, 'getblockcount' didn't return an u64.".to_string())
        })? as u32;
        let hash = BlockHash::from_str(
            self.make_node_request("getblockhash", &params!(json_height))?
                .as_str()
                .ok_or_else(|| {
                    BitcoindError::Custom(
                        "API break, 'getblockhash' didn't return a string.".to_string(),
                    )
                })?,
        )
        .map_err(|e| {
            BitcoindError::Custom(format!("Invalid blockhash given by 'getblockhash': {}", e))
        })?;

        Ok(BlockchainTip { height, hash })
    }

    pub fn synchronization_info(&self) -> Result<SyncInfo, BitcoindError> {
        let chaininfo = self.make_node_request("getblockchaininfo", &[])?;
        Ok(SyncInfo {
            headers: chaininfo
                .get("headers")
                .and_then(|h| h.as_u64())
                .ok_or_else(|| {
                    BitcoindError::Custom(
                        "No valid 'headers' in getblockchaininfo response?".to_owned(),
                    )
                })?,
            blocks: chaininfo
                .get("blocks")
                .and_then(|b| b.as_u64())
                .ok_or_else(|| {
                    BitcoindError::Custom(
                        "No valid 'blocks' in getblockchaininfo response?".to_owned(),
                    )
                })?,
            ibd: chaininfo
                .get("initialblockdownload")
                .and_then(|i| i.as_bool())
                .ok_or_else(|| {
                    BitcoindError::Custom(
                        "No valid 'initialblockdownload' in getblockchaininfo response?".to_owned(),
                    )
                })?,
            progress: chaininfo
                .get("verificationprogress")
                .and_then(|i| i.as_f64())
                .ok_or_else(|| {
                    BitcoindError::Custom(
                        "No valid 'initialblockdownload' in getblockchaininfo response?".to_owned(),
                    )
                })?,
        })
    }

    pub fn createwallet_startup(&self, wallet_path: String) -> Result<(), BitcoindError> {
        let res = self.make_node_request(
            "createwallet",
            &params!(
                Json::String(wallet_path),
                Json::Bool(true),             // watchonly
                Json::Bool(false),            // blank
                Json::String("".to_string()), // passphrase,
                Json::Bool(false),            // avoid_reuse
                Json::Bool(true),             // descriptors
                Json::Bool(true),             // load_on_startup
            ),
        )?;

        if res.get("name").is_some() {
            return Ok(());
        }

        Err(BitcoindError::Custom(format!(
            "Error creating wallet: '{:?}'",
            res.get("warning")
        )))
    }

    pub fn listwallets(&self) -> Result<Vec<String>, BitcoindError> {
        self.make_node_request("listwallets", &[])?
            .as_array()
            .ok_or_else(|| {
                BitcoindError::Custom(
                    "API break, 'listwallets' didn't return an array.".to_string(),
                )
            })
            .map(|vec| {
                vec.iter()
                    .map(|json_str| {
                        json_str
                            .as_str()
                            .unwrap_or_else(|| {
                                log::error!("'listwallets' contain a non-string value. Aborting.");
                                panic!("API break: 'listwallets' contains a non-string value");
                            })
                            .to_string()
                    })
                    .collect()
            })
    }

    pub fn loadwallet_startup(&self, wallet_path: String) -> Result<(), BitcoindError> {
        let res = self.make_node_request(
            "loadwallet",
            &params!(
                Json::String(wallet_path),
                Json::Bool(true), // load_on_startup
            ),
        )?;

        if res.get("name").is_some() {
            return Ok(());
        }

        Err(BitcoindError::Custom(format!(
            "Error loading wallet: '{:?}'",
            res.get("warning")
        )))
    }

    /// Constructs an `addr()` descriptor out of an address
    pub fn addr_descriptor(&self, address: &str) -> Result<String, BitcoindError> {
        let desc_wo_checksum = format!("addr({})", address);

        Ok(self
            .make_watchonly_request(
                "getdescriptorinfo",
                &params!(Json::String(desc_wo_checksum)),
            )?
            .get("descriptor")
            .ok_or_else(|| {
                BitcoindError::Custom("No 'descriptor' in 'getdescriptorinfo'".to_string())
            })?
            .as_str()
            .ok_or_else(|| {
                BitcoindError::Custom(
                    "'descriptor' in 'getdescriptorinfo' isn't a string anymore".to_string(),
                )
            })?
            .to_string())
    }

    fn bulk_import_descriptors(
        &self,
        descriptors: Vec<String>,
        timestamp: u32,
        label: String,
        fresh_wallet: bool,
    ) -> Result<(), BitcoindError> {
        let all_descriptors: Vec<Json> = descriptors
            .into_iter()
            .map(|desc| {
                let mut desc_map = serde_json::Map::with_capacity(3);
                desc_map.insert("desc".to_string(), Json::String(desc));
                // We set to "now" the timestamp for fresh wallet, as otherwise bitcoind
                // will rescan the last few blocks for each of them.
                desc_map.insert(
                    "timestamp".to_string(),
                    if fresh_wallet {
                        Json::String("now".to_string())
                    } else {
                        log::debug!("Not a fresh wallet, rescan *may* take some time.");
                        Json::Number(serde_json::Number::from(timestamp))
                    },
                );
                desc_map.insert("label".to_string(), Json::String(label.clone()));

                Json::Object(desc_map)
            })
            .collect();

        let res = self
            .make_watchonly_request("importdescriptors", &params!(Json::Array(all_descriptors)))?;
        if res.get(0).map(|x| x.get("success")) == Some(Some(&Json::Bool(true))) {
            return Ok(());
        }

        Err(BitcoindError::Custom(format!(
            "Error returned from 'importdescriptor': {:?}",
            res.get("error")
        )))
    }

    pub fn startup_import_deposit_descriptors(
        &self,
        descriptors: Vec<String>,
        timestamp: u32,
        fresh_wallet: bool,
    ) -> Result<(), BitcoindError> {
        self.bulk_import_descriptors(
            descriptors,
            timestamp,
            self.deposit_utxos_label(),
            fresh_wallet,
        )
    }

    pub fn startup_import_unvault_descriptors(
        &self,
        descriptors: Vec<String>,
        timestamp: u32,
        fresh_wallet: bool,
    ) -> Result<(), BitcoindError> {
        self.bulk_import_descriptors(
            descriptors,
            timestamp,
            self.unvault_utxos_label(),
            fresh_wallet,
        )
    }

    fn import_fresh_descriptor(
        &self,
        descriptor: String,
        label: String,
    ) -> Result<(), BitcoindError> {
        let mut desc_map = serde_json::Map::with_capacity(3);
        desc_map.insert("desc".to_string(), Json::String(descriptor));
        desc_map.insert("timestamp".to_string(), Json::String("now".to_string()));
        desc_map.insert("label".to_string(), Json::String(label));

        let res = self.make_watchonly_request(
            "importdescriptors",
            &params!(Json::Array(vec![Json::Object(desc_map,)])),
        )?;
        if res.get(0).map(|x| x.get("success")) == Some(Some(&Json::Bool(true))) {
            return Ok(());
        }

        Err(BitcoindError::Custom(format!(
            "In import_fresh descriptor, error returned from 'importdescriptor': {:?}",
            res.get("error")
        )))
    }

    pub fn import_fresh_deposit_descriptor(&self, descriptor: String) -> Result<(), BitcoindError> {
        self.import_fresh_descriptor(descriptor, self.deposit_utxos_label())
    }

    pub fn import_fresh_unvault_descriptor(&self, descriptor: String) -> Result<(), BitcoindError> {
        self.import_fresh_descriptor(descriptor, self.unvault_utxos_label())
    }

    // A routine to get the txid,vout pair out of a listunspent entry
    fn outpoint_from_utxo(&self, utxo: &Json) -> Result<OutPoint, BitcoindError> {
        let txid = utxo
            .get("txid")
            .ok_or_else(|| {
                BitcoindError::Custom(
                    "API break, 'listunspent' entry didn't contain a 'txid'.".to_string(),
                )
            })?
            .as_str()
            .ok_or_else(|| {
                BitcoindError::Custom(
                    "API break, 'listunspent' entry didn't contain a string 'txid'.".to_string(),
                )
            })?;
        let txid = Txid::from_str(txid).map_err(|e| {
            BitcoindError::Custom(format!(
                "Converting txid from str in 'listunspent': {}.",
                e.to_string()
            ))
        })?;
        let vout = utxo
            .get("vout")
            .ok_or_else(|| {
                BitcoindError::Custom(
                    "API break, 'listunspent' entry didn't contain a 'vout'.".to_string(),
                )
            })?
            .as_u64()
            .ok_or_else(|| {
                BitcoindError::Custom(
                    "API break, 'listunspent' entry didn't contain a valid 'vout'.".to_string(),
                )
            })?;
        Ok(OutPoint {
            txid,
            vout: vout as u32, // Bitcoin makes this safe
        })
    }

    /// Repeatedly called by our main loop to stay in sync with bitcoind.
    /// We take the currently known utxos, and return both the new deposits and the spent deposits.
    pub fn sync_deposits(
        &self,
        existing_utxos: &HashMap<OutPoint, DepositInfo>,
    ) -> Result<
        (
            HashMap<OutPoint, DepositInfo>, // new
            HashMap<OutPoint, DepositInfo>, // newly confirmed
            HashMap<OutPoint, DepositInfo>, // spent
        ),
        BitcoindError,
    > {
        let (mut new_deposits, mut confirmed_deposits) = (HashMap::new(), HashMap::new());
        // All seen utxos, if an utxo remains unseen by listunspent then it's spent.
        let mut spent_deposits = existing_utxos.clone();

        for utxo in self
            .make_watchonly_request(
                "listunspent",
                &params!(Json::Number(serde_json::Number::from(0))), // minconf
            )?
            .as_array()
            .ok_or_else(|| {
                BitcoindError::Custom(
                    "API break, 'listunspent' didn't return an array.".to_string(),
                )
            })?
        {
            if utxo.get("label") != Some(&self.deposit_utxos_label().into()) {
                continue;
            }
            let confirmations = utxo
                .get("confirmations")
                .ok_or_else(|| {
                    BitcoindError::Custom(
                        "API break, 'listunspent' entry didn't contain a 'confirmations'."
                            .to_string(),
                    )
                })?
                .as_u64()
                .ok_or_else(|| {
                    BitcoindError::Custom(
                        "API break, 'listunspent' entry didn't contain a valid 'confirmations'."
                            .to_string(),
                    )
                })?;

            let outpoint = self.outpoint_from_utxo(&utxo)?;
            // Not obvious at first sight:
            //  - spent_deposits == existing_deposits before the loop
            //  - listunspent won't send duplicated entries
            //  - remove() will return None if it was not present in the map, ie new deposit
            if let Some(utxo) = spent_deposits.remove(&outpoint) {
                // It may be present but still unconfirmed, though.
                if utxo.status == VaultStatus::Unconfirmed && confirmations >= MIN_CONF {
                    confirmed_deposits.insert(outpoint, utxo);
                }
                continue;
            }

            let address = utxo
                .get("address")
                .ok_or_else(|| {
                    BitcoindError::Custom(
                        "API break, 'listunspent' entry didn't contain an 'address'.".to_string(),
                    )
                })?
                .as_str()
                .ok_or_else(|| {
                    BitcoindError::Custom(
                        "API break, 'listunspent' entry didn't contain a string 'address'."
                            .to_string(),
                    )
                })?;
            let script_pubkey = Address::from_str(address)
                .map_err(|e| {
                    BitcoindError::Custom(format!(
                        "Could not parse 'address' from 'listunspent' entry: {}",
                        e.to_string()
                    ))
                })?
                .script_pubkey();
            let amount = utxo
                .get("amount")
                .ok_or_else(|| {
                    BitcoindError::Custom(
                        "API break, 'listunspent' entry didn't contain an 'amount'.".to_string(),
                    )
                })?
                .as_f64()
                .ok_or_else(|| {
                    BitcoindError::Custom(
                        "API break, 'listunspent' entry didn't contain a valid 'amount'."
                            .to_string(),
                    )
                })?;
            let value = Amount::from_btc(amount)
                .map_err(|e| {
                    BitcoindError::Custom(format!(
                        "Could not convert 'listunspent' entry's 'amount' to an Amount: {}",
                        e.to_string()
                    ))
                })?
                .as_sat();

            new_deposits.insert(
                outpoint,
                DepositInfo {
                    txo: TxOut {
                        value,
                        script_pubkey,
                    },
                    status: VaultStatus::Unconfirmed,
                },
            );
        }

        Ok((new_deposits, confirmed_deposits, spent_deposits))
    }

    /// Get the raw transaction as hex, the blockheight it was included in if
    /// it's confirmed, as well as the reception time.
    pub fn get_wallet_transaction(
        &self,
        txid: Txid,
    ) -> Result<(String, Option<u32>, u32), BitcoindError> {
        let res = self
            .make_watchonly_request("gettransaction", &params!(Json::String(txid.to_string())))?;
        let tx_hex = res
            .get("hex")
            .ok_or_else(|| {
                BitcoindError::Custom(format!(
                    "API break: no 'hex' in 'gettransaction' result (txid: {})",
                    txid
                ))
            })?
            .as_str()
            .ok_or_else(|| {
                BitcoindError::Custom("API break: 'hex' is not a string ????".to_string())
            })?
            .to_string();
        let blockheight = res.get("blockheight").map(|bh| bh.as_u64().unwrap() as u32);
        let received = res
            .get("timereceived")
            .ok_or_else(|| {
                BitcoindError::Custom(format!(
                    "API break: no 'time_received' in 'gettransaction' result (txid: {})",
                    txid
                ))
            })?
            .as_u64()
            .ok_or_else(|| {
                BitcoindError::Custom(format!(
                    "API break: invalid 'time_received' in 'gettransaction' result (txid: {})",
                    txid
                ))
            })? as u32;

        Ok((tx_hex, blockheight, received))
    }

    // This assumes wallet transactions, will error otherwise !
    fn previous_outpoints(&self, outpoint: &OutPoint) -> Result<Vec<OutPoint>, BitcoindError> {
        Ok(self
            .make_watchonly_request(
                "gettransaction",
                &params!(
                    Json::String(outpoint.txid.to_string()),
                    Json::Bool(true), // include_watchonly
                    Json::Bool(true), // verbose
                ),
            )?
            .get("decoded")
            .ok_or_else(|| {
                BitcoindError::Custom(
                    "API break: 'gettransaction' has no 'hex' in verbose mode?".to_string(),
                )
            })?
            .get("vin")
            .ok_or_else(|| {
                BitcoindError::Custom("API break: 'gettransaction' has no 'vin' ?".to_string())
            })?
            .as_array()
            .ok_or_else(|| {
                BitcoindError::Custom(
                    "API break: 'gettransaction' 'vin' isn't an array?".to_string(),
                )
            })?
            .iter()
            .filter_map(|txin| {
                Some(OutPoint {
                    txid: Txid::from_str(txin.get("txid")?.as_str()?).ok()?,
                    vout: txin.get("vout")?.as_u64()? as u32,
                })
            })
            .collect())
    }

    /// There is no good way to get the "spending transaction" from an utxo in bitcoind.
    /// So here we workaround it leveraging the fact we know the unvault address. So we list
    /// the unvault address transactions and check if one spent this outpoint to this address.
    pub fn unvault_from_vault(
        &self,
        vault_outpoint: &OutPoint,
        unvault_address: String,
    ) -> Result<Option<OutPoint>, BitcoindError> {
        let res = self.make_watchonly_request(
            "listunspent",
            &params!(
                Json::Number(serde_json::Number::from(0)),       // minconf
                Json::Number(serde_json::Number::from(9999999)), // maxconf (default)
                Json::Array(vec![Json::String(unvault_address)]),
            ),
        )?;
        let utxos = res.as_array().ok_or_else(|| {
            BitcoindError::Custom("API break: 'listunspent' didn't return an array".to_string())
        })?;

        for utxo in utxos {
            let outpoint = self.outpoint_from_utxo(&utxo)?;
            for prev_outpoint in self.previous_outpoints(&outpoint)? {
                if &prev_outpoint == vault_outpoint {
                    return Ok(Some(outpoint));
                }
            }
        }

        Ok(None)
    }
}

pub struct SyncInfo {
    pub headers: u64,
    pub blocks: u64,
    pub ibd: bool,
    pub progress: f64,
}

// Used in deposits cache for listunspent polling
#[derive(Debug, Clone)]
pub struct DepositInfo {
    pub txo: TxOut,
    pub status: VaultStatus,
}
