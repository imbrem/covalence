//! AWS S3 and S3-compatible backends, via `object_store::aws`.
//!
//! Supports custom endpoints for non-AWS providers (Wasabi, Backblaze B2,
//! Cloudflare R2, MinIO, etc.) through [`Config::custom`].

use std::ops::Range;

use async_trait::async_trait;
use bytes::Bytes;
use object_store::{GetOptions, GetRange, ObjectStore, ObjectStoreExt, PutPayload, path::Path};

use crate::{Error, KvStore, Meta, Result};

pub use object_store::aws::{AmazonS3, AmazonS3Builder};

/// Connection settings for an S3 or S3-compatible endpoint.
#[derive(Debug, Clone)]
pub struct Config {
    bucket: String,
    region: String,
    endpoint: Option<String>,
    access_key_id: Option<String>,
    secret_access_key: Option<String>,
    virtual_hosted_style: bool,
    allow_http: bool,
}

impl Config {
    /// AWS S3 with the default credential chain (env vars, `~/.aws/credentials`, IMDS).
    pub fn aws(bucket: impl Into<String>, region: impl Into<String>) -> Self {
        Self {
            bucket: bucket.into(),
            region: region.into(),
            endpoint: None,
            access_key_id: None,
            secret_access_key: None,
            virtual_hosted_style: true,
            allow_http: false,
        }
    }

    /// S3-compatible endpoint with explicit credentials.
    ///
    /// Defaults to **path-style addressing** (`endpoint/bucket/key`) since
    /// several third-party providers (notably Backblaze B2) don't reliably
    /// handle virtual-hosted-style for all bucket names.
    pub fn custom(
        endpoint: impl Into<String>,
        region: impl Into<String>,
        bucket: impl Into<String>,
        access_key_id: impl Into<String>,
        secret_access_key: impl Into<String>,
    ) -> Self {
        Self {
            bucket: bucket.into(),
            region: region.into(),
            endpoint: Some(endpoint.into()),
            access_key_id: Some(access_key_id.into()),
            secret_access_key: Some(secret_access_key.into()),
            virtual_hosted_style: false,
            allow_http: false,
        }
    }

    pub fn with_virtual_hosted_style(mut self, v: bool) -> Self {
        self.virtual_hosted_style = v;
        self
    }

    /// Allow plain HTTP (no TLS). Useful for local testing against `s3s-fs` / MinIO.
    pub fn with_allow_http(mut self, v: bool) -> Self {
        self.allow_http = v;
        self
    }

    /// Build an [`AmazonS3`] client.
    pub fn build(self) -> std::result::Result<AmazonS3, object_store::Error> {
        let mut builder = AmazonS3Builder::new()
            .with_bucket_name(self.bucket)
            .with_region(self.region)
            .with_virtual_hosted_style_request(self.virtual_hosted_style)
            .with_allow_http(self.allow_http);
        if let Some(endpoint) = self.endpoint {
            builder = builder.with_endpoint(endpoint);
        }
        if let Some(key) = self.access_key_id {
            builder = builder.with_access_key_id(key);
        }
        if let Some(secret) = self.secret_access_key {
            builder = builder.with_secret_access_key(secret);
        }
        builder.build()
    }
}

/// Wraps any [`object_store::ObjectStore`] as a [`KvStore`].
pub struct S3Kv<S = AmazonS3> {
    inner: S,
}

impl<S: ObjectStoreExt> S3Kv<S> {
    pub fn new(inner: S) -> Self {
        Self { inner }
    }

    pub fn into_inner(self) -> S {
        self.inner
    }

    pub fn inner(&self) -> &S {
        &self.inner
    }
}

fn parse_path(key: &str) -> Result<Path> {
    Path::parse(key).map_err(|e| Error::InvalidKey {
        key: key.to_string(),
        reason: e.to_string(),
    })
}

fn map_os_err(key: &str, e: object_store::Error) -> Error {
    use object_store::Error as OE;
    match e {
        OE::NotFound { .. } => Error::NotFound {
            key: key.to_string(),
        },
        OE::Unauthenticated { .. } | OE::PermissionDenied { .. } => Error::Auth(e.to_string()),
        _ => Error::Backend(e.to_string()),
    }
}

#[async_trait]
impl<S: ObjectStore> KvStore for S3Kv<S> {
    async fn get(&self, key: &str) -> Result<Bytes> {
        let path = parse_path(key)?;
        let result = self
            .inner
            .get(&path)
            .await
            .map_err(|e| map_os_err(key, e))?;
        result.bytes().await.map_err(|e| map_os_err(key, e))
    }

    async fn get_range(&self, key: &str, range: Range<u64>) -> Result<Bytes> {
        let path = parse_path(key)?;
        let opts = GetOptions {
            range: Some(GetRange::Bounded(range.start..range.end)),
            ..Default::default()
        };
        let result = self
            .inner
            .get_opts(&path, opts)
            .await
            .map_err(|e| map_os_err(key, e))?;
        result.bytes().await.map_err(|e| map_os_err(key, e))
    }

    async fn put(&self, key: &str, value: Bytes) -> Result<()> {
        let path = parse_path(key)?;
        self.inner
            .put(&path, PutPayload::from_bytes(value))
            .await
            .map_err(|e| map_os_err(key, e))?;
        Ok(())
    }

    async fn delete(&self, key: &str) -> Result<()> {
        let path = parse_path(key)?;
        match self.inner.delete(&path).await {
            Ok(()) => Ok(()),
            Err(object_store::Error::NotFound { .. }) => Ok(()),
            Err(e) => Err(map_os_err(key, e)),
        }
    }

    async fn head(&self, key: &str) -> Result<Meta> {
        let path = parse_path(key)?;
        let m = self
            .inner
            .head(&path)
            .await
            .map_err(|e| map_os_err(key, e))?;
        let modified = std::time::UNIX_EPOCH.checked_add(std::time::Duration::from_secs(
            m.last_modified.timestamp().max(0) as u64,
        ));
        Ok(Meta {
            size: m.size as u64,
            modified,
            etag: m.e_tag,
        })
    }
}
