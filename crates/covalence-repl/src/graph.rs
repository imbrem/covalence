//! Forsp ops for building and rendering `cov:graph` string diagrams.
//!
//! # Surface
//!
//! ```text
//! ;; Topology builder
//! graph-builder                                  → handle
//! $h "name" type-id "input"/"output" b-port      → $h
//! $h "payload" b-node                            → $h node-id
//! $h from-n from-p to-n to-p b-wire              → $h
//! $h b-finish                                    → graph-keyed-hash
//!
//! ;; Overlay constructors
//! "a" "b" "c" 3 labels                           → labels-keyed-hash
//! "pure" "ordered" 2 kinds                       → kinds-keyed-hash
//!
//! ;; Slot sentinels (32-byte values usable as label-/kind-slots)
//! absent-slot                                    → "no overlay" sentinel
//! all-pure                                       → "all pure" sentinel
//! all-ordered                                    → "all ordered" sentinel
//!
//! ;; Composition
//! $graph $label-slot $kind-slot string-diagram   → diagram-keyed-hash
//!
//! ;; Rendering
//! $hash svg                                      → svg-blob
//! $hash show                                     → $hash      ;; +inline preview
//! ```
//!
//! # Identity model
//!
//! Every command that produces an object pushes a **keyed identity** —
//! a 32-byte hash of the form `BLAKE3-keyed(tag, content_hash)` where
//! `content_hash = BLAKE3(bytes)`. The raw bytes are stored under
//! `content_hash` in the backend's blob store; the keyed hash is
//! registered in the backend's tag registry, which lets `show` / `svg`
//! / `preview` dispatch on **tag** rather than sniffing magic bytes.
//!
//! References inside a `StringDiagram` (graph slot and overlay slots)
//! are also keyed identities, so resolving a diagram involves two
//! lookups per reference: `lookup_tag` to recover the content hash,
//! then `get_blob` to fetch the bytes.
//!
//! # Inline previews
//!
//! `preview-on` enables a preview block after every command that
//! produces a renderable hash (`b-finish`, `string-diagram`). `show`
//! always emits one, ignoring the flag. Preview blocks are framed by
//! [`PREVIEW_BEGIN`] / [`PREVIEW_END`] sentinels so the web REPL can
//! splice them in as inline SVG; plain terminals see the markers.

use bytes::Bytes;
use covalence_forsp::{FCtx, FError};
use covalence_graph::{
    BytesGraph, BytesGraphBuilder, DagLayoutOpts, Edge, KIND_FLAGS_HASH_CTX, KindFlags,
    LABEL_LIST_HASH_CTX, LabelList, LayoutOpts, NodeId, NodeKind, ORDERED_HASH_CTX, Port, PortId,
    PortKind, Resolver, STRING_DIAGRAM_HASH_CTX, SlotRef, StringDiagram, TypeId, UniformTag,
    render_dag_svg, render_svg,
};
use covalence_hash::O256;
use covalence_shell::SyncBackend;

// ---------------------------------------------------------------------------
// Preview-block framing
// ---------------------------------------------------------------------------

/// Sentinel marker before an inline SVG preview. The web REPL splits
/// the output on this and renders the inner SVG. Plain terminals see
/// the literal marker.
pub const PREVIEW_BEGIN: &str = "\u{001E}cov-preview-svg\u{001E}";
/// Sentinel marker after an inline SVG preview block.
pub const PREVIEW_END: &str = "\u{001E}/cov-preview-svg\u{001E}";

/// Where graph commands append inline preview output. Constructed by
/// the dispatcher with the session's `preview_enabled` flag; commands
/// pass it through to [`emit_preview`].
pub struct PreviewSink<'a> {
    /// When false, [`emit_preview`] suppresses the SVG block.
    pub enabled: bool,
    pub output: &'a mut String,
}

/// Render `hash` and append a framed preview block if the sink is
/// enabled (or if `force` is true — `show` uses that to ignore the
/// `preview-on/off` flag).
fn emit_preview(
    sink: &mut PreviewSink<'_>,
    backend: &dyn SyncBackend,
    hash: &O256,
    force: bool,
) {
    if !sink.enabled && !force {
        return;
    }
    match render_hash_as_svg(backend, hash) {
        Ok(svg) => {
            sink.output.push_str(PREVIEW_BEGIN);
            sink.output.push('\n');
            sink.output.push_str(&svg);
            sink.output.push('\n');
            sink.output.push_str(PREVIEW_END);
            sink.output.push('\n');
        }
        Err(e) => {
            sink.output.push_str(&format!("preview: {e}\n"));
        }
    }
}

// ---------------------------------------------------------------------------
// Builder-handle state
// ---------------------------------------------------------------------------

/// Open builder handles for the topology side of the REPL. A handle is
/// just a `u32` index into [`Self::builders`]; entries become `None`
/// after `b-finish` consumes them. New handles reuse vacant slots.
pub struct GraphState {
    builders: Vec<Option<OpenBuilder>>,
}

struct OpenBuilder {
    inner: BytesGraphBuilder,
    /// Ports buffered by `b-port` calls; consumed by the next `b-node`.
    pending_ports: Vec<Port>,
}

impl GraphState {
    pub fn new() -> Self {
        Self { builders: Vec::new() }
    }

    fn alloc(&mut self) -> u32 {
        let new = OpenBuilder {
            inner: BytesGraphBuilder::new(),
            pending_ports: Vec::new(),
        };
        if let Some((idx, slot)) =
            self.builders.iter_mut().enumerate().find(|(_, s)| s.is_none())
        {
            *slot = Some(new);
            return idx as u32;
        }
        let id = self.builders.len() as u32;
        self.builders.push(Some(new));
        id
    }

    fn get_mut(&mut self, handle: u32) -> Result<&mut OpenBuilder, FError> {
        self.builders
            .get_mut(handle as usize)
            .and_then(|s| s.as_mut())
            .ok_or_else(|| FError::Parse(format!("unknown builder handle: {handle}")))
    }

    fn take(&mut self, handle: u32) -> Result<OpenBuilder, FError> {
        self.builders
            .get_mut(handle as usize)
            .and_then(|s| s.take())
            .ok_or_else(|| FError::Parse(format!("unknown builder handle: {handle}")))
    }
}

impl Default for GraphState {
    fn default() -> Self {
        Self::new()
    }
}

// ---------------------------------------------------------------------------
// Forsp value helpers
// ---------------------------------------------------------------------------

fn pop_int(ctx: &mut FCtx<'_>) -> Result<i32, FError> {
    let v = ctx.try_pop()?;
    ctx.heap.try_as_int(v)
}

fn pop_u32(ctx: &mut FCtx<'_>, what: &'static str) -> Result<u32, FError> {
    u32::try_from(pop_int(ctx)?)
        .map_err(|_| FError::Parse(format!("{what} must be a non-negative u32")))
}

fn pop_handle(ctx: &mut FCtx<'_>) -> Result<u32, FError> {
    pop_u32(ctx, "builder handle")
}

fn push_int(ctx: &mut FCtx<'_>, n: i32) {
    let v = ctx.heap.int(n);
    ctx.push(v);
}

fn pop_string(ctx: &mut FCtx<'_>, what: &'static str) -> Result<String, FError> {
    let blob = ctx.try_pop_blob()?;
    String::from_utf8(blob).map_err(|e| FError::Parse(format!("{what} must be valid UTF-8: {e}")))
}

fn parse_port_kind(s: &str) -> Result<PortKind, FError> {
    match s {
        "input" | "in" => Ok(PortKind::Input),
        "output" | "out" => Ok(PortKind::Output),
        _ => Err(FError::Parse(format!(
            "port kind must be 'input' or 'output', got {s:?}"
        ))),
    }
}

fn parse_node_kind(s: &str) -> Result<NodeKind, FError> {
    NodeKind::parse(s)
        .ok_or_else(|| FError::Parse(format!("node kind must be 'pure' or 'ordered', got {s:?}")))
}

/// Store `bytes` and register them under `tag`, returning the keyed
/// identity. Used by every command that produces a graph object.
fn store_and_tag(
    backend: &dyn SyncBackend,
    bytes: &[u8],
    tag: &str,
) -> Result<O256, FError> {
    let content = backend
        .store_blob(bytes)
        .map_err(|e| FError::Parse(e.to_string()))?;
    backend
        .register_tag(tag, content)
        .map_err(|e| FError::Parse(e.to_string()))
}

// ---------------------------------------------------------------------------
// Topology builder commands
// ---------------------------------------------------------------------------

/// `graph-builder` → handle
pub fn cmd_graph_builder(state: &mut GraphState, ctx: &mut FCtx<'_>) -> Result<(), FError> {
    let id = state.alloc();
    push_int(ctx, id as i32);
    Ok(())
}

/// `$h "name" type-id "input"/"output" b-port` → $h
pub fn cmd_b_port(state: &mut GraphState, ctx: &mut FCtx<'_>) -> Result<(), FError> {
    let kind = parse_port_kind(&pop_string(ctx, "port kind")?)?;
    let type_id = TypeId(pop_int(ctx)? as u64);
    let name = pop_string(ctx, "port name")?;
    let handle = pop_handle(ctx)?;
    state.get_mut(handle)?.pending_ports.push(Port {
        name,
        type_id,
        kind,
    });
    push_int(ctx, handle as i32);
    Ok(())
}

/// `$h "payload" b-node` → $h node-id
pub fn cmd_b_node(state: &mut GraphState, ctx: &mut FCtx<'_>) -> Result<(), FError> {
    let payload = ctx.try_pop_blob()?;
    let handle = pop_handle(ctx)?;
    let builder = state.get_mut(handle)?;
    let ports = std::mem::take(&mut builder.pending_ports);
    let id = builder.inner.add_node(ports, Bytes::from(payload));
    push_int(ctx, handle as i32);
    push_int(ctx, id.0 as i32);
    Ok(())
}

/// `$h from-n from-p to-n to-p b-wire` → $h
pub fn cmd_b_wire(state: &mut GraphState, ctx: &mut FCtx<'_>) -> Result<(), FError> {
    let to_port = pop_u32(ctx, "to_port")?;
    let to_node = pop_u32(ctx, "to_node")?;
    let from_port = pop_u32(ctx, "from_port")?;
    let from_node = pop_u32(ctx, "from_node")?;
    let handle = pop_handle(ctx)?;
    state
        .get_mut(handle)?
        .inner
        .wire(Edge {
            from_node: NodeId(from_node),
            from_port: PortId(from_port),
            to_node: NodeId(to_node),
            to_port: PortId(to_port),
        })
        .map_err(|e| FError::Parse(e.to_string()))?;
    push_int(ctx, handle as i32);
    Ok(())
}

/// `$h b-finish` → graph-keyed-hash. Consumes the builder, stores the
/// canonical bytes, registers the `ORDERED_HASH_CTX` tag, and emits a
/// preview if enabled.
pub fn cmd_b_finish(
    state: &mut GraphState,
    backend: &dyn SyncBackend,
    ctx: &mut FCtx<'_>,
    mut preview: PreviewSink<'_>,
) -> Result<(), FError> {
    let handle = pop_handle(ctx)?;
    let graph = state
        .take(handle)?
        .inner
        .finish()
        .map_err(|e| FError::Parse(e.to_string()))?;
    let keyed = store_and_tag(backend, &graph.to_bytes(), ORDERED_HASH_CTX)?;
    emit_preview(&mut preview, backend, &keyed, false);
    ctx.push_hash(keyed);
    Ok(())
}

// ---------------------------------------------------------------------------
// Overlay constructors
// ---------------------------------------------------------------------------

/// Pop `n` blobs from the stack and interpret each as a UTF-8 string,
/// preserving the original push order. `n` is itself popped first.
fn pop_n_strings(ctx: &mut FCtx<'_>, what: &'static str) -> Result<Vec<String>, FError> {
    let n = pop_u32(ctx, "count")?;
    let mut acc = Vec::with_capacity(n as usize);
    for _ in 0..n {
        acc.push(pop_string(ctx, what)?);
    }
    acc.reverse();
    Ok(acc)
}

/// `"a" "b" "c" 3 labels` → labels-keyed-hash
pub fn cmd_labels(backend: &dyn SyncBackend, ctx: &mut FCtx<'_>) -> Result<(), FError> {
    let labels = LabelList::from_strings(pop_n_strings(ctx, "label")?);
    let keyed = store_and_tag(backend, &labels.to_bytes(), LABEL_LIST_HASH_CTX)?;
    ctx.push_hash(keyed);
    Ok(())
}

/// `"pure" "ordered" 2 kinds` → kinds-keyed-hash
pub fn cmd_kinds(backend: &dyn SyncBackend, ctx: &mut FCtx<'_>) -> Result<(), FError> {
    let strs = pop_n_strings(ctx, "node kind")?;
    let kinds = strs
        .iter()
        .map(|s| parse_node_kind(s))
        .collect::<Result<Vec<_>, _>>()?;
    let keyed = store_and_tag(backend, &KindFlags::new(kinds).to_bytes(), KIND_FLAGS_HASH_CTX)?;
    ctx.push_hash(keyed);
    Ok(())
}

// ---------------------------------------------------------------------------
// Slot sentinels + composition
// ---------------------------------------------------------------------------

fn push_slot(ctx: &mut FCtx<'_>, slot: SlotRef) {
    ctx.push_hash(O256::from_bytes(slot.to_o256_bytes()));
}

/// `absent-slot` → all-zero "no overlay" slot value.
pub fn cmd_absent_slot(ctx: &mut FCtx<'_>) -> Result<(), FError> {
    push_slot(ctx, SlotRef::Absent);
    Ok(())
}

/// `all-pure` → "every node is pure" sentinel slot value.
pub fn cmd_all_pure(ctx: &mut FCtx<'_>) -> Result<(), FError> {
    push_slot(ctx, SlotRef::Uniform(UniformTag::AllPure));
    Ok(())
}

/// `all-ordered` → "every node is ordered" sentinel slot value.
pub fn cmd_all_ordered(ctx: &mut FCtx<'_>) -> Result<(), FError> {
    push_slot(ctx, SlotRef::Uniform(UniformTag::AllOrdered));
    Ok(())
}

/// `$graph-keyed $label-slot $kind-slot string-diagram` → diagram-keyed-hash.
/// The graph slot must be a keyed identity (from `b-finish`); label
/// and kind slots may be either a keyed identity or one of the
/// sentinel values pushed by `absent-slot` / `all-pure` / `all-ordered`.
pub fn cmd_string_diagram(
    backend: &dyn SyncBackend,
    ctx: &mut FCtx<'_>,
    mut preview: PreviewSink<'_>,
) -> Result<(), FError> {
    let kinds = decode_slot(ctx.try_pop_hash()?)?;
    let labels = decode_slot(ctx.try_pop_hash()?)?;
    let graph = ctx.try_pop_hash()?;
    let sd = StringDiagram { graph, labels, kinds };
    let keyed = store_and_tag(backend, &sd.to_bytes(), STRING_DIAGRAM_HASH_CTX)?;
    emit_preview(&mut preview, backend, &keyed, false);
    ctx.push_hash(keyed);
    Ok(())
}

fn decode_slot(h: O256) -> Result<SlotRef, FError> {
    SlotRef::from_o256_bytes(*h.as_bytes()).map_err(|e| FError::Parse(e.to_string()))
}

/// `$hash show` → $hash. Always emits a preview block, ignoring the
/// session's `preview-on/off` flag; leaves the hash on the stack so the
/// caller can keep using it.
pub fn cmd_show(
    backend: &dyn SyncBackend,
    ctx: &mut FCtx<'_>,
    mut preview: PreviewSink<'_>,
) -> Result<(), FError> {
    let hash = ctx.try_pop_hash()?;
    emit_preview(&mut preview, backend, &hash, true);
    ctx.push_hash(hash);
    Ok(())
}

// ---------------------------------------------------------------------------
// Rendering
// ---------------------------------------------------------------------------

/// Resolver that walks a `StringDiagram`'s slot references by
/// performing the two-step `lookup_tag → get_blob` indirection for
/// every keyed identity it's asked to fetch.
struct BackendResolver<'a> {
    backend: &'a dyn SyncBackend,
}

impl Resolver for BackendResolver<'_> {
    fn get(&self, keyed: &O256) -> Option<Vec<u8>> {
        let (_, content) = self.backend.lookup_tag(keyed).ok().flatten()?;
        self.backend.get_blob(&content).ok().flatten()
    }
}

/// `$keyed-hash svg` → svg-blob.
pub fn cmd_svg(backend: &dyn SyncBackend, ctx: &mut FCtx<'_>) -> Result<(), FError> {
    let hash = ctx.try_pop_hash()?;
    let svg = render_hash_as_svg(backend, &hash)?;
    ctx.push_blob(svg.into_bytes());
    Ok(())
}

/// Render whatever object `hash` names as standalone SVG markup.
/// Dispatch is by **tag**: the backend's tag registry tells us whether
/// the hash is a topology blob, a string diagram, or an overlay.
pub fn render_hash_as_svg(backend: &dyn SyncBackend, hash: &O256) -> Result<String, FError> {
    let (tag, content_hash) = backend
        .lookup_tag(hash)
        .map_err(parse_err)?
        .ok_or_else(|| FError::Parse(format!("blob {hash} is not registered with a tag")))?;
    let bytes = backend
        .get_blob(&content_hash)
        .map_err(parse_err)?
        .ok_or_else(|| FError::Parse(format!("content blob {content_hash} not found")))?;
    render_object(backend, &tag, &bytes)
}

/// Dispatch on `tag` to produce an SVG for the given `bytes`.
fn render_object(backend: &dyn SyncBackend, tag: &str, bytes: &[u8]) -> Result<String, FError> {
    match tag {
        ORDERED_HASH_CTX => {
            // Bare topology → layered DAG (dots + lines).
            let graph = BytesGraph::from_bytes(bytes).map_err(parse_err)?;
            Ok(render_dag_svg(&graph, &DagLayoutOpts::default()))
        }
        STRING_DIAGRAM_HASH_CTX => {
            let sd = StringDiagram::from_bytes(bytes).map_err(parse_err)?;
            let resolver = BackendResolver { backend };
            let graph_bytes = resolver
                .get(&sd.graph)
                .ok_or_else(|| FError::Parse(format!("graph {} not found", sd.graph)))?;
            let graph = BytesGraph::from_bytes(&graph_bytes).map_err(parse_err)?;
            let resolved = sd.resolve(&graph, &resolver).map_err(parse_err)?;
            Ok(render_svg(&resolved, &LayoutOpts::default()))
        }
        LABEL_LIST_HASH_CTX => {
            let ll = LabelList::from_bytes(bytes).map_err(parse_err)?;
            Err(FError::Parse(format!(
                "label-list overlay ({} entries) — not directly renderable; combine with a string diagram",
                ll.len()
            )))
        }
        KIND_FLAGS_HASH_CTX => {
            let kf = KindFlags::from_bytes(bytes).map_err(parse_err)?;
            Err(FError::Parse(format!(
                "kind-flags overlay ({} entries) — not directly renderable",
                kf.len()
            )))
        }
        other => Err(FError::Parse(format!("no renderer for tag {other}"))),
    }
}

fn parse_err(e: impl std::fmt::Display) -> FError {
    FError::Parse(e.to_string())
}
