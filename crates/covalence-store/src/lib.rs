use wasm_bindgen::prelude::*;

/// Fetch a blob from the iroh network given a blob ticket string.
///
/// Returns the raw bytes of the blob as a `Uint8Array`.
#[wasm_bindgen]
pub async fn fetch_blob(ticket_str: &str) -> Result<js_sys::Uint8Array, JsValue> {
    fetch_blob_inner(ticket_str)
        .await
        .map_err(|e| JsValue::from_str(&format!("{e:#}")))
}

async fn fetch_blob_inner(ticket_str: &str) -> anyhow::Result<js_sys::Uint8Array> {
    use iroh_blobs::{
        BlobsProtocol,
        api::downloader::{Downloader, Shuffled},
        ticket::BlobTicket,
    };

    let ticket: BlobTicket = ticket_str.parse()?;

    // Create an iroh endpoint using the default N0 relay presets.
    // In the browser this uses relay-only (WebSocket) connections.
    let endpoint = iroh::Endpoint::bind(iroh::endpoint::presets::N0).await?;

    // In-memory blob store (only option in the browser).
    let store = iroh_blobs::store::mem::MemStore::default();

    // Wire up the blobs protocol on the router so we can receive data.
    let blobs = BlobsProtocol::new(store.as_ref(), None);
    let router = iroh::protocol::Router::builder(endpoint)
        .accept(iroh_blobs::ALPN, blobs)
        .spawn();

    // Download the blob from the node advertised in the ticket.
    let downloader = Downloader::new(store.as_ref(), router.endpoint());
    downloader
        .download(
            ticket.hash_and_format(),
            Shuffled::new(vec![ticket.addr().id]),
        )
        .await?;

    // Read the downloaded bytes back from the store.
    let bytes = store.get_bytes(ticket.hash()).await?;

    // Shut down networking.
    router.shutdown().await?;

    Ok(js_sys::Uint8Array::from(bytes.as_ref()))
}
