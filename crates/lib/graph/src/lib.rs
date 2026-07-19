//! Ordered, typed, payload-polymorphic graph + string-diagram overlays.
//!
//! @covalence-api {"id":"A0008","title":"Graphs and graph interchange","status":"experimental","dependsOn":[]}
//!
//! Three layers:
//!
//! 1. [`Graph<P>`] — ordered port topology + opaque payloads. This is
//!    the only thing the WIT API and the WASM linker see. Identity is
//!    the canonical byte encoding (see [`canonical`]), hashed under the
//!    [`canonical::ORDERED_HASH_CTX`] or
//!    [`canonical::UNORDERED_HASH_CTX`] BLAKE3 contexts.
//! 2. [`overlay`] — independent blobs that decorate a graph without
//!    changing its identity: [`overlay::LabelList`] (per-node labels)
//!    and [`overlay::KindFlags`] (per-node Pure/Ordered classification).
//! 3. [`string_diagram::StringDiagram`] — a tiny composite holding the
//!    underlying graph hash plus references (or sentinels) to the
//!    overlays. This is what gets rendered as a string-diagram.
//!
//! # Why split labels and kinds out
//!
//! The same topology can be presented under many labellings ("the same
//! WASM linker graph viewed as the user's diagram", "viewed as a
//! cached intermediate") and many effect classifications (all-pure for
//! the linker, mixed for a category-theoretic interpretation). Keeping
//! these as separate content-addressed blobs lets each be shared,
//! cached, and substituted independently.
//!
//! # Premonoidal reading
//!
//! Nodes form an *ordered sequence* — first added, first initialised.
//! Two graphs with the same `(nodes-as-set, edges-as-set)` but a
//! different insertion order are not equal. The intended interpretation
//! is a symmetric **premonoidal** category (Power & Robinson 1997);
//! reordering changes program meaning when nodes have effects. The
//! state-thread visualisation derives from this: consecutive nodes
//! marked `Ordered` in the overlay share a dashed red wire that
//! represents the implicit effect ordering.
//!
//! # Linearity
//!
//! Input ports are *linear* (each wired at most once); output ports
//! fan out freely. A consumer wanting strict cartesian semantics
//! inserts explicit copy nodes; strict linear semantics is enforced at
//! the consumer's layer with a single-outgoing-edge check.

// TODO(cov:graph.dot-full, major): Extend the bounded DOT interchange subset to ports, subgraphs, HTML labels, chained edges, and the complete attribute grammar.
pub mod canonical;
pub mod interchange;
pub mod networkx;
pub mod overlay;
pub mod render;
pub mod string_diagram;
pub mod theory;

pub use canonical::{
    BuildError, BytesGraph, BytesGraphBuilder, CANONICAL_MAGIC, CANONICAL_VERSION, DecodeError,
    Edge, FromPartsError, Graph, GraphBuilder, Node, NodeId, ORDERED_HASH_CTX, Port, PortId,
    PortKind, TypeId, UNORDERED_HASH_CTX, WireError,
};
pub use overlay::{KIND_FLAGS_HASH_CTX, KindFlags, LABEL_LIST_HASH_CTX, LabelList, NodeKind};
pub use render::{DagLayoutOpts, LayoutOpts, render_dag_svg, render_svg};
pub use string_diagram::{
    OverlayMap, OverlayStorage, ResolveError, ResolvedDiagram, Resolver, STRING_DIAGRAM_HASH_CTX,
    SlotRef, StringDiagram, StringDiagramBuilder, UniformTag,
};

#[cfg(test)]
mod tests;
