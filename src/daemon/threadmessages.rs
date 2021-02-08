use crate::revaultd::VaultStatus;
use revault_tx::{
    bitcoin::{util::bip32::ChildNumber, Address, Amount, OutPoint, Txid},
    transactions::{
        CancelTransaction, EmergencyTransaction, SpendTransaction, UnvaultEmergencyTransaction,
        UnvaultTransaction,
    },
};

use std::sync::mpsc::SyncSender;

/// Incoming from RPC server thread
#[derive(Debug)]
pub enum RpcMessageIn {
    Shutdown,
    // Network, blockheight, sync progress
    GetInfo(SyncSender<(String, u32, f64)>),
    ListVaults(
        (Option<Vec<VaultStatus>>, Option<Vec<OutPoint>>),
        SyncSender<Vec<ListVaultsEntry>>,
    ),
    DepositAddr(SyncSender<Address>),
    GetRevocationTxs(
        OutPoint,
        // None if the deposit does not exist
        SyncSender<
            Option<(
                CancelTransaction,
                EmergencyTransaction,
                UnvaultEmergencyTransaction,
            )>,
        >,
    ),
    // Returns None if the transactions could all be stored succesfully
    RevocationTxs(
        (
            OutPoint,
            CancelTransaction,
            EmergencyTransaction,
            UnvaultEmergencyTransaction,
        ),
        SyncSender<Option<String>>,
    ),
    ListTransactions(
        Option<Vec<OutPoint>>,
        SyncSender<
            // None if the deposit does not exist
            Vec<VaultTransactions>,
        >,
    ),
}

/// Outgoing to the bitcoind poller thread
#[derive(Debug)]
pub enum BitcoindMessageOut {
    Shutdown,
    SyncProgress(SyncSender<f64>),
    WalletTransaction(Txid, SyncSender<Option<WalletTransaction>>),
}

/// Outgoing to the signature fetcher thread
#[derive(Debug)]
pub enum SigFetcherMessageOut {
    Shutdown,
}

#[derive(Debug)]
pub struct WalletTransaction {
    pub hex: String,
    // None if unconfirmed
    pub blockheight: Option<u32>,
    pub received_time: u32,
}

#[derive(Debug)]
pub struct TransactionResource<T> {
    // None if not broadcast
    pub wallet_tx: Option<WalletTransaction>,
    pub tx: T,
    pub is_signed: bool,
}

#[derive(Debug)]
pub struct VaultTransactions {
    pub outpoint: OutPoint,
    pub deposit: WalletTransaction,
    pub unvault: TransactionResource<UnvaultTransaction>,
    // None if not spending
    pub spend: Option<TransactionResource<SpendTransaction>>,
    pub cancel: TransactionResource<CancelTransaction>,
    pub emergency: TransactionResource<EmergencyTransaction>,
    pub unvault_emergency: TransactionResource<UnvaultEmergencyTransaction>,
}

#[derive(Debug)]
pub struct ListVaultsEntry {
    pub amount: Amount,
    pub status: VaultStatus,
    pub deposit_outpoint: OutPoint,
    pub derivation_index: ChildNumber,
    pub address: Address,
    pub updated_at: u32,
}
