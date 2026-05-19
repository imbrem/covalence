#[cfg(feature = "sync")]
mod sync_client;
#[cfg(feature = "sync")]
pub use sync_client::SyncHttpBackend;

#[cfg(feature = "async")]
mod async_client;
#[cfg(feature = "async")]
pub use async_client::AsyncHttpBackend;
