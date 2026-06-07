use super::*;
use bytes::Bytes;

fn out(name: &str, ty: u64) -> Port {
    Port {
        name: name.into(),
        type_id: TypeId(ty),
        kind: PortKind::Output,
    }
}
fn inp(name: &str, ty: u64) -> Port {
    Port {
        name: name.into(),
        type_id: TypeId(ty),
        kind: PortKind::Input,
    }
}

fn simple_pair() -> Graph<&'static str> {
    let mut b = GraphBuilder::new();
    let src = b.add_node(vec![out("o", 1)], "src");
    let snk = b.add_node(vec![inp("i", 1)], "snk");
    b.wire(Edge {
        from_node: src,
        from_port: PortId(0),
        to_node: snk,
        to_port: PortId(0),
    })
    .unwrap();
    b.finish().unwrap()
}

#[test]
fn build_and_inspect() {
    let g = simple_pair();
    assert_eq!(g.node_count(), 2);
    assert_eq!(g.edge_count(), 1);
    assert_eq!(g.get_node(NodeId(0)).unwrap().payload, "src");
    assert_eq!(g.get_node(NodeId(1)).unwrap().payload, "snk");
    assert_eq!(g.edges_from(NodeId(0), None).count(), 1);
    assert_eq!(g.edges_into(NodeId(1), None).count(), 1);
    assert_eq!(g.edges_from(NodeId(1), None).count(), 0);
}

#[test]
fn insertion_order_matters() {
    let g1 = simple_pair();
    let g2 = {
        let mut b = GraphBuilder::new();
        let snk = b.add_node(vec![inp("i", 1)], "snk");
        let src = b.add_node(vec![out("o", 1)], "src");
        b.wire(Edge {
            from_node: src,
            from_port: PortId(0),
            to_node: snk,
            to_port: PortId(0),
        })
        .unwrap();
        b.finish().unwrap()
    };
    assert!(!g1.equal(&g2));
}

#[test]
fn type_mismatch_rejected() {
    let mut b = GraphBuilder::<()>::new();
    let src = b.add_node(vec![out("o", 1)], ());
    let snk = b.add_node(vec![inp("i", 2)], ());
    let err = b
        .wire(Edge {
            from_node: src,
            from_port: PortId(0),
            to_node: snk,
            to_port: PortId(0),
        })
        .unwrap_err();
    assert_eq!(err, WireError::TypeMismatch(TypeId(1), TypeId(2)));
}

#[test]
fn kind_mismatch_rejected() {
    let mut b = GraphBuilder::<()>::new();
    let a = b.add_node(vec![inp("i", 1)], ());
    let c = b.add_node(vec![out("o", 1)], ());
    let err = b
        .wire(Edge {
            from_node: a,
            from_port: PortId(0),
            to_node: c,
            to_port: PortId(0),
        })
        .unwrap_err();
    assert_eq!(err, WireError::KindMismatch);
}

#[test]
fn input_linearity() {
    let mut b = GraphBuilder::<()>::new();
    let s1 = b.add_node(vec![out("o", 1)], ());
    let s2 = b.add_node(vec![out("o", 1)], ());
    let k = b.add_node(vec![inp("i", 1)], ());
    b.wire(Edge {
        from_node: s1,
        from_port: PortId(0),
        to_node: k,
        to_port: PortId(0),
    })
    .unwrap();
    let err = b
        .wire(Edge {
            from_node: s2,
            from_port: PortId(0),
            to_node: k,
            to_port: PortId(0),
        })
        .unwrap_err();
    assert_eq!(err, WireError::AlreadyWired(k, PortId(0)));
}

#[test]
fn output_fans_out() {
    let mut b = GraphBuilder::<()>::new();
    let src = b.add_node(vec![out("o", 1)], ());
    let k1 = b.add_node(vec![inp("i", 1)], ());
    let k2 = b.add_node(vec![inp("i", 1)], ());
    b.wire(Edge {
        from_node: src,
        from_port: PortId(0),
        to_node: k1,
        to_port: PortId(0),
    })
    .unwrap();
    b.wire(Edge {
        from_node: src,
        from_port: PortId(0),
        to_node: k2,
        to_port: PortId(0),
    })
    .unwrap();
    let g = b.finish().unwrap();
    assert_eq!(g.edges_from(src, None).count(), 2);
}

#[test]
fn finish_rejects_unwired_inputs() {
    let mut b = GraphBuilder::<()>::new();
    b.add_node(vec![inp("i", 1)], ());
    let err = b.finish().unwrap_err();
    assert_eq!(err, BuildError::UnwiredInput(NodeId(0), PortId(0)));
}

fn bytes_pair() -> BytesGraph {
    let mut b = BytesGraphBuilder::new();
    let src = b.add_node(vec![out("o", 1)], Bytes::from_static(b"src"));
    let snk = b.add_node(vec![inp("i", 1)], Bytes::from_static(b"snk"));
    b.wire(Edge {
        from_node: src,
        from_port: PortId(0),
        to_node: snk,
        to_port: PortId(0),
    })
    .unwrap();
    b.finish().unwrap()
}

#[test]
fn canonical_roundtrip() {
    let g = bytes_pair();
    let bytes = g.to_bytes();
    let g2 = BytesGraph::from_bytes(&bytes).unwrap();
    assert!(g.equal(&g2));
}

#[test]
fn canonical_starts_with_magic() {
    let bytes = bytes_pair().to_bytes();
    assert_eq!(&bytes[..4], &CANONICAL_MAGIC);
    assert_eq!(bytes[4], CANONICAL_VERSION);
}

#[test]
fn ordered_and_unordered_hashes_differ() {
    let g = bytes_pair();
    assert_ne!(g.ordered_hash(), g.unordered_hash());
}

#[test]
fn bad_magic_rejected() {
    let err = BytesGraph::from_bytes(b"NOPE\x01\x00").unwrap_err();
    assert!(matches!(err, DecodeError::BadMagic { .. }));
}

#[test]
fn truncated_rejected() {
    let err = BytesGraph::from_bytes(b"COV").unwrap_err();
    assert!(matches!(err, DecodeError::Truncated { .. }));
}

// ------------------ overlay tests ------------------

#[test]
fn label_list_roundtrips() {
    let ll = LabelList::new(vec![
        Some("first".into()),
        None,
        Some("third with spaces".into()),
    ]);
    let bytes = ll.to_bytes();
    let back = LabelList::from_bytes(&bytes).unwrap();
    assert_eq!(ll, back);
    assert_eq!(back.get(0), Some("first"));
    assert_eq!(back.get(1), None);
    assert_eq!(back.get(2), Some("third with spaces"));
}

#[test]
fn kind_flags_roundtrips_and_iter() {
    let kf = KindFlags::new(vec![
        NodeKind::Ordered,
        NodeKind::Pure,
        NodeKind::Ordered,
        NodeKind::Ordered,
    ]);
    let bytes = kf.to_bytes();
    let back = KindFlags::from_bytes(&bytes).unwrap();
    assert_eq!(kf, back);
    let collected: Vec<NodeKind> = back.iter().collect();
    assert_eq!(
        collected,
        vec![
            NodeKind::Ordered,
            NodeKind::Pure,
            NodeKind::Ordered,
            NodeKind::Ordered,
        ]
    );
    let ord: Vec<u32> = back.ordered_node_indices().collect();
    assert_eq!(ord, vec![0, 2, 3]);
}

#[test]
fn kind_flags_uniform_round_trips() {
    let kf = KindFlags::uniform(5, NodeKind::Ordered);
    assert_eq!(kf.is_uniform_as(), Some(NodeKind::Ordered));
    let back = KindFlags::from_bytes(&kf.to_bytes()).unwrap();
    assert_eq!(kf, back);
}

#[test]
fn kind_flags_canonical_for_uniform() {
    let kf = KindFlags::new(vec![NodeKind::Pure; 9]);
    let back = KindFlags::from_bytes(&kf.to_bytes()).unwrap();
    assert_eq!(kf, back);
    assert_eq!(back.is_uniform_as(), Some(NodeKind::Pure));
}

// ------------------ string-diagram tests ------------------

#[test]
fn string_diagram_no_overlays() {
    let g = bytes_pair();
    let sd = StringDiagramBuilder::new(&g).build();
    assert_eq!(sd.graph, g.ordered_hash());
    assert!(matches!(sd.labels, SlotRef::Absent));
    assert!(matches!(sd.kinds, SlotRef::Absent));
    let bytes = sd.to_bytes();
    let back = StringDiagram::from_bytes(&bytes).unwrap();
    assert_eq!(sd, back);
}

#[test]
fn string_diagram_uniform_kind_uses_sentinel() {
    let g = bytes_pair();
    let sd = StringDiagramBuilder::new(&g)
        .with_uniform_kind(NodeKind::Ordered)
        .build();
    assert!(matches!(sd.kinds, SlotRef::Uniform(UniformTag::AllOrdered)));
    let back = StringDiagram::from_bytes(&sd.to_bytes()).unwrap();
    assert_eq!(sd, back);
}

#[test]
fn string_diagram_mixed_kinds_use_overlay() {
    let g = bytes_pair();
    let kf = KindFlags::new(vec![NodeKind::Ordered, NodeKind::Pure]);
    let mut store = OverlayMap::default();
    let sd = StringDiagramBuilder::new(&g)
        .with_kinds(kf.clone())
        .build_with(&mut store);
    let h = match sd.kinds {
        SlotRef::Hash(h) => h,
        other => panic!("expected hash slot, got {other:?}"),
    };
    assert_eq!(h, kf.hash());
    assert!(store.blobs.contains_key(&h));
}

#[test]
fn string_diagram_kind_flags_all_same_collapse_to_uniform() {
    let g = bytes_pair();
    // KindFlags is "all ordered"; builder should fold to AllOrdered sentinel.
    let kf = KindFlags::new(vec![NodeKind::Ordered, NodeKind::Ordered]);
    let mut store = OverlayMap::default();
    let sd = StringDiagramBuilder::new(&g)
        .with_kinds(kf)
        .build_with(&mut store);
    assert!(matches!(sd.kinds, SlotRef::Uniform(UniformTag::AllOrdered)));
    assert!(store.blobs.is_empty(), "uniform overlays shouldn't be stored");
}

#[test]
fn string_diagram_labels_round_trip() {
    let g = bytes_pair();
    let labels = LabelList::new(vec![Some("source".into()), Some("sink".into())]);
    let mut store = OverlayMap::default();
    let sd = StringDiagramBuilder::new(&g)
        .with_labels(labels.clone())
        .build_with(&mut store);
    let lh = match sd.labels {
        SlotRef::Hash(h) => h,
        other => panic!("expected hash slot, got {other:?}"),
    };
    assert_eq!(lh, labels.hash());
    assert!(store.blobs.contains_key(&lh));
    let back = StringDiagram::from_bytes(&sd.to_bytes()).unwrap();
    assert_eq!(sd, back);
}

#[test]
fn string_diagram_resolve_into_renderable() {
    let g = bytes_pair();
    let labels = LabelList::new(vec![Some("source".into()), Some("sink".into())]);
    let kinds = KindFlags::new(vec![NodeKind::Ordered, NodeKind::Pure]);
    let mut store = OverlayMap::default();
    let sd = StringDiagramBuilder::new(&g)
        .with_labels(labels)
        .with_kinds(kinds)
        .build_with(&mut store);
    let resolved = sd.resolve(&g, &store).unwrap();
    assert_eq!(resolved.label_for(0), "source");
    assert_eq!(resolved.label_for(1), "sink");
    assert_eq!(resolved.kind_of(0), NodeKind::Ordered);
    assert_eq!(resolved.kind_of(1), NodeKind::Pure);
}

#[test]
fn slot_ref_sentinel_layout() {
    let zero = SlotRef::Absent.to_o256_bytes();
    assert_eq!(zero, [0u8; 32]);
    let pure = SlotRef::Uniform(UniformTag::AllPure).to_o256_bytes();
    assert_eq!(pure[0], 0xFF);
    assert_eq!(pure[1], 1);
    assert!(pure[2..].iter().all(|&b| b == 0));
    let ordered = SlotRef::Uniform(UniformTag::AllOrdered).to_o256_bytes();
    assert_eq!(ordered[1], 2);
}

// ------------------ renderer smoke test ------------------

#[test]
fn render_svg_smoke() {
    let g = bytes_pair();
    let kinds = KindFlags::new(vec![NodeKind::Ordered, NodeKind::Pure]);
    let labels = LabelList::new(vec![Some("src".into()), Some("snk".into())]);
    let mut store = OverlayMap::default();
    let sd = StringDiagramBuilder::new(&g)
        .with_labels(labels)
        .with_kinds(kinds)
        .build_with(&mut store);
    let resolved = sd.resolve(&g, &store).unwrap();
    let svg = render_svg(&resolved, &LayoutOpts::default());
    assert!(svg.starts_with("<svg"));
    assert!(svg.contains("src"));
    assert!(svg.contains("snk"));
    // State thread should appear only when there's at least one ordered node.
    assert!(svg.contains("state-thread"));
}

#[test]
fn render_dag_svg_uses_circles_not_rects() {
    let g = bytes_pair();
    let svg = render_dag_svg(&g, &DagLayoutOpts::default());
    assert!(svg.starts_with("<svg"));
    // DAG view: dots (<circle>) not boxes (<rect>).
    assert!(svg.contains("<circle"), "expected circle, got: {svg}");
    assert!(!svg.contains("<rect "), "DAG view shouldn't draw rect boxes: {svg}");
    // Two nodes => two node groups + at least one edge path.
    assert_eq!(svg.matches("<g class=\"node\"").count(), 2);
    assert!(svg.contains("<path "));
}

#[test]
fn render_dag_svg_collapses_multiedges() {
    // Build a graph where a single output fans out via two ports into
    // two inputs of the same target: only one DAG edge should appear.
    let mut b = BytesGraphBuilder::new();
    let src = b.add_node(vec![out("a", 1), out("b", 1)], Bytes::from_static(b""));
    let snk = b.add_node(vec![inp("x", 1), inp("y", 1)], Bytes::from_static(b""));
    b.wire(Edge {
        from_node: src,
        from_port: PortId(0),
        to_node: snk,
        to_port: PortId(0),
    })
    .unwrap();
    b.wire(Edge {
        from_node: src,
        from_port: PortId(1),
        to_node: snk,
        to_port: PortId(1),
    })
    .unwrap();
    let g = b.finish().unwrap();
    let svg = render_dag_svg(&g, &DagLayoutOpts::default());
    // Two wires, but in the collapsed DAG view it's a single visible path.
    assert_eq!(svg.matches("<path ").count(), 1, "got: {svg}");
}

#[test]
fn render_svg_no_overlays() {
    let g = bytes_pair();
    let sd = StringDiagramBuilder::new(&g).build();
    let store = OverlayMap::default();
    let resolved = sd.resolve(&g, &store).unwrap();
    let svg = render_svg(&resolved, &LayoutOpts::default());
    assert!(svg.starts_with("<svg"));
    // No labels → falls back to "#0", "#1".
    assert!(svg.contains("#0"));
    assert!(svg.contains("#1"));
}
