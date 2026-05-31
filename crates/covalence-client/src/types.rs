use serde::Deserialize;

#[derive(Deserialize)]
pub(crate) struct HashResponse {
    pub hash: String,
}

#[derive(Deserialize)]
pub(crate) struct BlobStatsResponse {
    pub count: Option<usize>,
}

#[derive(Deserialize)]
pub(crate) struct DecideResponse {
    pub result: String,
    #[serde(default)]
    pub proved: Vec<String>,
}
