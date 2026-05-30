//! Git smart HTTP v2 transport.
//!
//! Implements ref discovery, `ls-refs`, and `fetch` over the git smart HTTP
//! protocol version 2.

use std::io::{self, BufRead, BufReader};

use crate::clone::pktline::{self, PktLine};

/// Server capabilities discovered during handshake.
#[derive(Debug, Default)]
pub struct Capabilities {
    pub version: u8,
    pub commands: Vec<String>,
    pub agent: Option<String>,
    pub object_format: Option<String>,
}

/// A remote ref returned by `ls-refs`.
#[derive(Debug, Clone)]
#[allow(dead_code)]
pub struct RemoteRef {
    pub name: String,
    pub oid: covalence_hash::gix_hash::ObjectId,
    pub symref_target: Option<String>,
    pub peeled: Option<covalence_hash::gix_hash::ObjectId>,
}

/// Parsed URL components for a git remote.
#[derive(Debug, Clone)]
pub struct GitUrl {
    pub base_url: String,
}

impl GitUrl {
    /// Parse a git HTTP(S) URL.
    ///
    /// Strips trailing `.git` and `/` for consistency.
    pub fn parse(url: &str) -> Self {
        let base = url.trim_end_matches('/').to_string();
        Self { base_url: base }
    }

    pub fn info_refs_url(&self) -> String {
        format!("{}/info/refs?service=git-upload-pack", self.base_url)
    }

    pub fn upload_pack_url(&self) -> String {
        format!("{}/git-upload-pack", self.base_url)
    }
}

/// Discover server capabilities via `GET /info/refs?service=git-upload-pack`.
pub fn discover(agent: &ureq::Agent, url: &GitUrl) -> io::Result<Capabilities> {
    let resp = agent
        .get(&url.info_refs_url())
        .header("Git-Protocol", "version=2")
        .call()
        .map_err(ureq_err)?;

    let mut reader = BufReader::new(resp.into_body().into_reader());
    parse_capabilities(&mut reader)
}

/// Parse capabilities from the info/refs response.
fn parse_capabilities(r: &mut impl BufRead) -> io::Result<Capabilities> {
    let mut caps = Capabilities::default();

    // First section: service announcement (v2 servers may include this).
    let lines = pktline::read_until_flush(r)?;
    for line in &lines {
        if let PktLine::Data(data) = line {
            let text = String::from_utf8_lossy(data);
            let text = text.trim();
            if text.starts_with("# service=") {
                continue;
            }
            if text.starts_with("version ") {
                if let Ok(v) = text["version ".len()..].trim().parse::<u8>() {
                    caps.version = v;
                }
                continue;
            }
            parse_cap_line(&mut caps, text);
        }
    }

    // If version wasn't in the first section, read the next section.
    if caps.version == 0 {
        let lines2 = pktline::read_until_flush(r)?;
        for line in &lines2 {
            if let PktLine::Data(data) = line {
                let text = String::from_utf8_lossy(data);
                let text = text.trim();
                if text.starts_with("version ") {
                    if let Ok(v) = text["version ".len()..].trim().parse::<u8>() {
                        caps.version = v;
                    }
                    continue;
                }
                parse_cap_line(&mut caps, text);
            }
        }
    }

    Ok(caps)
}

fn parse_cap_line(caps: &mut Capabilities, line: &str) {
    if let Some(agent) = line.strip_prefix("agent=") {
        caps.agent = Some(agent.to_string());
    } else if let Some(fmt) = line.strip_prefix("object-format=") {
        caps.object_format = Some(fmt.to_string());
    } else if !line.contains('=') && !line.starts_with('#') && !line.is_empty() {
        // Bare capability names are command names (ls-refs, fetch, etc.)
        caps.commands.push(line.to_string());
    }
}

/// Execute `ls-refs` to list remote references.
pub fn ls_refs(
    agent: &ureq::Agent,
    url: &GitUrl,
    ref_prefixes: &[String],
) -> io::Result<Vec<RemoteRef>> {
    let mut body = Vec::new();
    pktline::write_pkt_line(&mut body, b"command=ls-refs\n")?;
    pktline::write_pkt_line(&mut body, b"agent=covalence\n")?;
    pktline::write_pkt_line(&mut body, b"object-format=sha1\n")?;
    pktline::write_delim(&mut body)?;
    pktline::write_pkt_line(&mut body, b"peel\n")?;
    pktline::write_pkt_line(&mut body, b"symrefs\n")?;
    for prefix in ref_prefixes {
        let line = format!("ref-prefix {prefix}\n");
        pktline::write_pkt_line(&mut body, line.as_bytes())?;
    }
    pktline::write_flush(&mut body)?;

    let resp = agent
        .post(&url.upload_pack_url())
        .header("Content-Type", "application/x-git-upload-pack-request")
        .header("Git-Protocol", "version=2")
        .send(&body[..])
        .map_err(ureq_err)?;

    let mut reader = BufReader::new(resp.into_body().into_reader());
    let lines = pktline::read_until_flush(&mut reader)?;
    let mut refs = Vec::new();

    for line in lines {
        if let PktLine::Data(data) = line {
            if let Some(r) = parse_ref_line(&data) {
                refs.push(r);
            }
        }
    }

    Ok(refs)
}

/// Parse a single ref line: `<oid> <name>[ symref-target:<target>][ peeled:<oid>]`
fn parse_ref_line(data: &[u8]) -> Option<RemoteRef> {
    let text = std::str::from_utf8(data).ok()?;
    let text = text.trim_end_matches('\n');
    let mut parts = text.splitn(2, ' ');
    let oid_hex = parts.next()?;
    let rest = parts.next()?;

    let oid = covalence_hash::gix_hash::ObjectId::from_hex(oid_hex.as_bytes()).ok()?;

    let mut name = rest;
    let mut symref_target = None;
    let mut peeled = None;

    // Attributes are space-separated after the ref name.
    if let Some(idx) = rest.find(" symref-target:") {
        name = &rest[..idx];
        let attr_start = idx + " symref-target:".len();
        let attr_end = rest[attr_start..]
            .find(' ')
            .map(|i| attr_start + i)
            .unwrap_or(rest.len());
        symref_target = Some(rest[attr_start..attr_end].to_string());
    }
    if let Some(idx) = rest.find(" peeled:") {
        if name.len() > idx {
            name = &rest[..idx];
        }
        let attr_start = idx + " peeled:".len();
        let attr_end = rest[attr_start..]
            .find(' ')
            .map(|i| attr_start + i)
            .unwrap_or(rest.len());
        if let Ok(p) =
            covalence_hash::gix_hash::ObjectId::from_hex(rest[attr_start..attr_end].as_bytes())
        {
            peeled = Some(p);
        }
    }
    // Re-extract name (first token of rest)
    let name = name.split(' ').next().unwrap_or(name);

    Some(RemoteRef {
        name: name.to_string(),
        oid,
        symref_target,
        peeled,
    })
}

/// Sideband-demuxed packfile data from a fetch response.
pub struct FetchResponse {
    /// Raw packfile bytes (sideband channel 1).
    pub pack_data: Vec<u8>,
    /// Shallow boundary OIDs sent by the server.
    pub shallow_oids: Vec<covalence_hash::gix_hash::ObjectId>,
}

/// Execute the `fetch` command to download objects.
pub fn fetch(
    agent: &ureq::Agent,
    url: &GitUrl,
    wants: &[covalence_hash::gix_hash::ObjectId],
    depth: Option<u32>,
    filter: Option<&str>,
) -> io::Result<FetchResponse> {
    if wants.is_empty() {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "no wants specified",
        ));
    }

    let mut body = Vec::new();
    pktline::write_pkt_line(&mut body, b"command=fetch\n")?;
    pktline::write_pkt_line(&mut body, b"agent=covalence\n")?;
    pktline::write_pkt_line(&mut body, b"object-format=sha1\n")?;
    pktline::write_delim(&mut body)?;
    pktline::write_pkt_line(&mut body, b"ofs-delta\n")?;

    for want in wants {
        let line = format!("want {want}\n");
        pktline::write_pkt_line(&mut body, line.as_bytes())?;
    }

    if let Some(d) = depth {
        let line = format!("deepen {d}\n");
        pktline::write_pkt_line(&mut body, line.as_bytes())?;
    }

    if let Some(f) = filter {
        let line = format!("filter {f}\n");
        pktline::write_pkt_line(&mut body, line.as_bytes())?;
    }

    pktline::write_pkt_line(&mut body, b"done\n")?;
    pktline::write_flush(&mut body)?;

    let resp = agent
        .post(&url.upload_pack_url())
        .header("Content-Type", "application/x-git-upload-pack-request")
        .header("Git-Protocol", "version=2")
        .send(&body[..])
        .map_err(ureq_err)?;

    let mut reader = BufReader::new(resp.into_body().into_reader());
    parse_fetch_response(&mut reader)
}

/// Parse the fetch response with sideband demuxing.
fn parse_fetch_response(r: &mut impl BufRead) -> io::Result<FetchResponse> {
    let mut pack_data = Vec::new();
    let mut shallow_oids = Vec::new();
    let mut in_packfile_section = false;

    loop {
        let pkt = match pktline::read_pkt_line(r)? {
            None => break,
            Some(PktLine::Flush) => {
                if in_packfile_section {
                    break;
                }
                continue;
            }
            Some(PktLine::ResponseEnd) => break,
            Some(PktLine::Delim) => {
                in_packfile_section = true;
                continue;
            }
            Some(pkt) => pkt,
        };

        if let PktLine::Data(data) = pkt {
            if !in_packfile_section {
                // Pre-packfile section: shallow/unshallow lines, acknowledgments
                let text = String::from_utf8_lossy(&data);
                let text = text.trim();
                if text == "packfile" {
                    in_packfile_section = true;
                    continue;
                }
                if let Some(hex) = text.strip_prefix("shallow ") {
                    if let Ok(oid) =
                        covalence_hash::gix_hash::ObjectId::from_hex(hex.trim().as_bytes())
                    {
                        shallow_oids.push(oid);
                    }
                }
                continue;
            }

            // Sideband demux: first byte is the channel.
            if data.is_empty() {
                continue;
            }
            match data[0] {
                1 => {
                    // Channel 1: packfile data
                    pack_data.extend_from_slice(&data[1..]);
                }
                2 => {
                    // Channel 2: progress (ignore for now, could forward to callback)
                }
                3 => {
                    // Channel 3: error
                    let msg = String::from_utf8_lossy(&data[1..]);
                    return Err(io::Error::new(
                        io::ErrorKind::Other,
                        format!("server error: {msg}"),
                    ));
                }
                _ => {
                    // Unknown channel — ignore
                }
            }
        }
    }

    Ok(FetchResponse {
        pack_data,
        shallow_oids,
    })
}

fn ureq_err(e: ureq::Error) -> io::Error {
    io::Error::new(io::ErrorKind::Other, e.to_string())
}
