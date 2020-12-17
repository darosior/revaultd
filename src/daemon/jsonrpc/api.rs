use crate::{revaultd::VaultStatus, threadmessages::*};
use common::VERSION;

use revault_tx::{bitcoin::OutPoint, transactions::RevaultTransaction};

use std::{
    process,
    str::FromStr,
    sync::{
        atomic::{AtomicBool, Ordering},
        mpsc::{self, Sender},
        Arc,
    },
};

use jsonrpc_core::Error as JsonRpcError;
use jsonrpc_derive::rpc;
use serde_json::json;

#[derive(Clone)]
pub struct JsonRpcMetaData {
    pub tx: Sender<RpcMessageIn>,
    pub shutdown: Arc<AtomicBool>,
}
impl jsonrpc_core::Metadata for JsonRpcMetaData {}

impl JsonRpcMetaData {
    pub fn from_tx(tx: Sender<RpcMessageIn>) -> Self {
        JsonRpcMetaData {
            tx,
            shutdown: Arc::from(AtomicBool::from(false)),
        }
    }

    pub fn is_shutdown(&self) -> bool {
        self.shutdown.load(Ordering::Relaxed)
    }

    pub fn shutdown(&self) {
        // Relaxed is fine, worse case we just stop at the next iteration on ARM
        self.shutdown.store(true, Ordering::Relaxed);
    }
}

#[rpc(server)]
pub trait RpcApi {
    type Metadata;

    /// Stops the daemon
    #[rpc(meta, name = "stop")]
    fn stop(&self, meta: Self::Metadata) -> jsonrpc_core::Result<()>;

    /// Get informations about the daemon
    #[rpc(meta, name = "getinfo")]
    fn getinfo(&self, meta: Self::Metadata) -> jsonrpc_core::Result<serde_json::Value>;

    /// Get a list of current vaults, which can be sorted by txids or status
    #[rpc(meta, name = "listvaults")]
    fn listvaults(
        &self,
        meta: Self::Metadata,
        statuses: Option<Vec<String>>,
        outpoints: Option<Vec<String>>,
    ) -> jsonrpc_core::Result<serde_json::Value>;

    /// Get an address to receive funds to the stakeholders' descriptor
    #[rpc(meta, name = "getdepositaddress")]
    fn getdepositaddress(&self, meta: Self::Metadata) -> jsonrpc_core::Result<serde_json::Value>;

    /// Get the cancel and both emergency transactions for a vault identified by deposit txid.
    #[rpc(meta, name = "getrevocationtxs")]
    fn getrevocationtxs(
        &self,
        meta: Self::Metadata,
        txid: String,
    ) -> jsonrpc_core::Result<serde_json::Value>;

    /// Retrieve the onchain transactions of a vault with the given deposit outpoint
    #[rpc(meta, name = "getonchaintxs")]
    fn getonchaintxs(
        &self,
        meta: Self::Metadata,
        outpoint: String,
    ) -> jsonrpc_core::Result<serde_json::Value>;
}

// Some parsing boilerplate

macro_rules! parse_outpoint {
    ($outpoint:expr) => {
        OutPoint::from_str(&$outpoint).map_err(|e| {
            JsonRpcError::invalid_params(format!(
                "'{}' is not a valid outpoint ({})",
                &$outpoint,
                e.to_string()
            ))
        })
    };
}

macro_rules! parse_vault_status {
    ($status:expr) => {
        VaultStatus::from_str(&$status).map_err(|_| {
            JsonRpcError::invalid_params(format!("'{}' is not a valid vault status", &$status))
        })
    };
}

pub struct RpcImpl;
impl RpcApi for RpcImpl {
    type Metadata = JsonRpcMetaData;

    fn stop(&self, meta: JsonRpcMetaData) -> jsonrpc_core::Result<()> {
        meta.shutdown();
        meta.tx.send(RpcMessageIn::Shutdown).unwrap();
        Ok(())
    }

    fn getinfo(&self, meta: Self::Metadata) -> jsonrpc_core::Result<serde_json::Value> {
        let (response_tx, response_rx) = mpsc::sync_channel(0);
        meta.tx
            .send(RpcMessageIn::GetInfo(response_tx))
            .unwrap_or_else(|e| {
                log::error!("Sending 'getinfo' to main thread: {:?}", e);
                process::exit(1);
            });
        let (net, height, progress) = response_rx.recv().unwrap_or_else(|e| {
            log::error!("Receiving 'getinfo' result from main thread: {:?}", e);
            process::exit(1);
        });

        Ok(json!({
            "version": VERSION.to_string(),
            "network": net,
            "blockheight": height,
            "sync": progress,
        }))
    }

    fn listvaults(
        &self,
        meta: Self::Metadata,
        statuses: Option<Vec<String>>,
        outpoints: Option<Vec<String>>,
    ) -> jsonrpc_core::Result<serde_json::Value> {
        let statuses = if let Some(statuses) = statuses {
            // If they give an empty array, it's not that they don't want any result, but rather
            // that they don't want this filter to be taken into account!
            if statuses.len() > 0 {
                Some(
                    statuses
                        .into_iter()
                        .map(|status_str| parse_vault_status!(status_str))
                        .collect::<jsonrpc_core::Result<Vec<VaultStatus>>>()?,
                )
            } else {
                None
            }
        } else {
            None
        };
        let outpoints = if let Some(outpoints) = outpoints {
            // If they give an empty array, it's not that they don't want any result, but rather
            // that they don't want this filter to be taken into account!
            if outpoints.len() > 0 {
                Some(
                    outpoints
                        .into_iter()
                        .map(|op_str| parse_outpoint!(op_str))
                        .collect::<jsonrpc_core::Result<Vec<OutPoint>>>()?,
                )
            } else {
                None
            }
        } else {
            None
        };

        let (response_tx, response_rx) = mpsc::sync_channel(0);
        meta.tx
            .send(RpcMessageIn::ListVaults((statuses, outpoints), response_tx))
            .unwrap_or_else(|e| {
                log::error!("Sending 'listvaults' to main thread: {:?}", e);
                process::exit(1);
            });
        let vaults = response_rx.recv().unwrap_or_else(|e| {
            log::error!("Receiving 'listvaults' result from main thread: {:?}", e);
            process::exit(1);
        });
        let vaults: Vec<serde_json::Value> = vaults
            .into_iter()
            .map(|(value, status, txid, vout)| {
                json!({
                    "amount": value,
                    "status": status,
                    "txid": txid,
                    "vout": vout,
                })
            })
            .collect();

        Ok(json!({ "vaults": vaults }))
    }

    fn getdepositaddress(&self, meta: Self::Metadata) -> jsonrpc_core::Result<serde_json::Value> {
        let (response_tx, response_rx) = mpsc::sync_channel(0);
        meta.tx
            .send(RpcMessageIn::DepositAddr(response_tx))
            .unwrap_or_else(|e| {
                log::error!("Sending 'depositaddr' to main thread: {:?}", e);
                process::exit(1);
            });
        let address = response_rx.recv().unwrap_or_else(|e| {
            log::error!("Receiving 'depositaddr' result from main thread: {:?}", e);
            process::exit(1);
        });

        Ok(json!({ "address": address.to_string() }))
    }

    fn getrevocationtxs(
        &self,
        meta: Self::Metadata,
        outpoint: String,
    ) -> jsonrpc_core::Result<serde_json::Value> {
        let outpoint = parse_outpoint!(outpoint)?;
        let (response_tx, response_rx) = mpsc::sync_channel(0);
        meta.tx
            .send(RpcMessageIn::GetRevocationTxs(outpoint, response_tx))
            .unwrap_or_else(|e| {
                log::error!("Sending 'getrevocationtxs' to main thread: {:?}", e);
                process::exit(1);
            });
        let (cancel_tx, emer_tx, unemer_tx) = response_rx
            .recv()
            .unwrap_or_else(|e| {
                log::error!("Receiving 'getrevocationtxs' from main thread: {:?}", e);
                process::exit(1);
            })
            .ok_or_else(|| {
                JsonRpcError::invalid_params(format!(
                    "'{}' does not refer to a known and confirmed vault",
                    &outpoint,
                ))
            })?;

        Ok(json!({
            "cancel_tx": cancel_tx.as_psbt_string().expect("We just derived it"),
            "emergency_tx": emer_tx.as_psbt_string().expect("We just derived it"),
            "emergency_unvault_tx": unemer_tx.as_psbt_string().expect("We just derived it"),
        }))
    }

    fn getonchaintxs(
        &self,
        meta: Self::Metadata,
        outpoint: String,
    ) -> jsonrpc_core::Result<serde_json::Value> {
        let outpoint = parse_outpoint!(outpoint)?;
        let (response_tx, response_rx) = mpsc::sync_channel(0);
        meta.tx
            .send(RpcMessageIn::GetOnchainTxs(outpoint, response_tx))
            .unwrap_or_else(|e| {
                log::error!("Sending 'getonchaintxs' to main thread: {:?}", e);
                process::exit(1);
            });
        let (unvault_tx, spend_tx, cancel_tx, emergency_tx, emergency_unvault_tx) =
            response_rx.recv().unwrap_or_else(|e| {
                log::error!("Receiving 'getrevocationtxs' from main thread: {:?}", e);
                process::exit(1);
            });

        let mut res = serde_json::Map::with_capacity(5);
        if let Some(unvault_tx) = unvault_tx {
            res.insert(
                "unvault_tx".to_string(),
                unvault_tx.as_psbt_string().expect("From db").into(),
            );
        }
        if let Some(spend_tx) = spend_tx {
            res.insert(
                "spend_tx".to_string(),
                spend_tx.as_psbt_string().expect("From db").into(),
            );
        }
        if let Some(cancel_tx) = cancel_tx {
            res.insert(
                "cancel_tx".to_string(),
                cancel_tx.as_psbt_string().expect("From db").into(),
            );
        }
        if let Some(emergency_tx) = emergency_tx {
            res.insert(
                "emergency_tx".to_string(),
                emergency_tx.as_psbt_string().expect("From db").into(),
            );
        }
        if let Some(emergency_unvault_tx) = emergency_unvault_tx {
            res.insert(
                "emergency_unvault_tx".to_string(),
                emergency_unvault_tx
                    .as_psbt_string()
                    .expect("From db")
                    .into(),
            );
        }

        Ok(res.into())
    }
}
