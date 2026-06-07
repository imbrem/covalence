//! Integration tests for the graph + string-diagram REPL commands.

use covalence_repl::Session;
use covalence_shell::Kernel;

fn fresh_session() -> Session {
    Session::new(Box::new(Kernel::new()), false, false)
}

#[test]
fn build_simple_graph_and_render() {
    let mut s = fresh_session();
    // Build a 2-node, 1-edge graph: `src` → `snk`.
    // graph-builder → $h
    // "o" "out" type 1 → port
    // "src" payload → node 0
    // "i" "in"  type 1 → port
    // "snk" payload → node 1
    // wire 0:0 → 1:0
    // b-finish → hash
    let script = r#"
        graph-builder $h
        ^h "o" 1 "output" b-port
        ^h "src" b-node $id0
        ^h "i" 1 "input" b-port
        ^h "snk" b-node $id1
        ^h 0 0 1 0 b-wire
        ^h b-finish $g
    "#;
    let _ = s.eval(script);
    // Verify by rendering: $g svg → svg blob, then print to inspect.
    let out = s.eval("^g svg print");
    assert!(out.contains("<svg"), "svg start expected, got: {out}");
    assert!(out.contains("#0"), "node 0 fallback label expected: {out}");
    assert!(out.contains("#1"), "node 1 fallback label expected: {out}");
}

#[test]
fn compose_string_diagram_with_labels_and_kinds() {
    let mut s = fresh_session();
    let prelude = r#"
        graph-builder $h
        ^h "o" 1 "output" b-port
        ^h "src" b-node $_
        ^h "i" 1 "input" b-port
        ^h "snk" b-node $_
        ^h 0 0 1 0 b-wire
        ^h b-finish $g
        "source" "sink" 2 labels $ll
        "ordered" "pure" 2 kinds $kk
        ^g ^ll ^kk string-diagram $sd
    "#;
    let _ = s.eval(prelude);
    let out = s.eval("^sd svg print");
    assert!(out.contains("source"), "labeled SVG should mention 'source': {out}");
    assert!(out.contains("sink"), "labeled SVG should mention 'sink': {out}");
    assert!(out.contains("state-thread"), "ordered node should yield a state thread: {out}");
}

#[test]
fn uniform_kind_sentinel_does_not_store_overlay() {
    let mut s = fresh_session();
    let script = r#"
        graph-builder $h
        ^h "o" 1 "output" b-port
        ^h "src" b-node $_
        ^h "i" 1 "input" b-port
        ^h "snk" b-node $_
        ^h 0 0 1 0 b-wire
        ^h b-finish $g
        absent-slot $absent
        all-ordered $ord
        ^g ^absent ^ord string-diagram $sd
        ^sd preview
    "#;
    let out = s.eval(script);
    assert!(out.contains("all-ordered"), "preview should report all-ordered slot: {out}");
    assert!(out.contains("absent"), "preview should report absent labels: {out}");
}

#[test]
fn preview_on_auto_renders_after_string_diagram() {
    let mut s = fresh_session();
    let script = r#"
        preview-on
        graph-builder $h
        ^h "o" 1 "output" b-port
        ^h "src" b-node $_
        ^h "i" 1 "input" b-port
        ^h "snk" b-node $_
        ^h 0 0 1 0 b-wire
        ^h b-finish $g
        absent-slot $absent
        all-pure $ap
        ^g ^absent ^ap string-diagram $sd
    "#;
    let out = s.eval(script);
    // Both b-finish AND string-diagram should auto-emit previews.
    let count = out.matches("cov-preview-svg").count();
    assert!(count >= 2, "expected at least 2 preview markers, got {count}: {out}");
    assert!(out.contains("<svg"), "preview should contain SVG markup: {out}");
}

#[test]
fn show_command_emits_preview_regardless_of_flag() {
    let mut s = fresh_session();
    let script = r#"
        graph-builder $h
        ^h "o" 1 "output" b-port
        ^h "src" b-node $_
        ^h "i" 1 "input" b-port
        ^h "snk" b-node $_
        ^h 0 0 1 0 b-wire
        ^h b-finish $g
        ^g show
    "#;
    let out = s.eval(script);
    assert!(out.contains("cov-preview-svg"), "show should emit preview marker: {out}");
    assert!(out.contains("<svg"), "show should emit SVG: {out}");
    // Bare COVG topology → DAG view: circles, no rect boxes.
    assert!(out.contains("<circle"), "DAG preview should use circles: {out}");
    assert!(!out.contains("<rect "), "DAG preview should not draw rect boxes: {out}");
}

#[test]
fn string_diagram_preview_uses_box_renderer() {
    let mut s = fresh_session();
    let script = r#"
        graph-builder $h
        ^h "o" 1 "output" b-port
        ^h "src" b-node $_
        ^h "i" 1 "input" b-port
        ^h "snk" b-node $_
        ^h 0 0 1 0 b-wire
        ^h b-finish $g
        "source" "sink" 2 labels $ll
        absent-slot $absent
        all-pure $ap
        ^g ^ll ^ap string-diagram $sd
        ^sd show
    "#;
    let out = s.eval(script);
    // String-diagram preview uses the box renderer.
    assert!(out.contains("<rect"), "string-diagram should draw boxes: {out}");
    assert!(out.contains("source"), "labels should be visible: {out}");
}

#[test]
fn preview_off_is_default() {
    let mut s = fresh_session();
    let script = r#"
        graph-builder $h
        ^h "o" 1 "output" b-port
        ^h "src" b-node $_
        ^h "i" 1 "input" b-port
        ^h "snk" b-node $_
        ^h 0 0 1 0 b-wire
        ^h b-finish $g
    "#;
    let out = s.eval(script);
    assert!(
        !out.contains("cov-preview-svg"),
        "previews are off by default: {out}"
    );
}

#[test]
fn b_finish_returns_keyed_identity_not_content_hash() {
    let mut s = fresh_session();
    let script = r#"
        graph-builder $h
        ^h "o" 1 "output" b-port
        ^h "src" b-node $_
        ^h "i" 1 "input" b-port
        ^h "snk" b-node $_
        ^h 0 0 1 0 b-wire
        ^h b-finish $g
        ^g preview
    "#;
    let out = s.eval(script);
    // The preview is reached via the tag-dispatch path, which decodes
    // the topology blob and reports its node/edge counts.
    assert!(out.contains("graph topology"), "expected graph identification: {out}");
    assert!(out.contains("2 nodes"), "expected node count in preview: {out}");
}

#[test]
fn string_diagram_dispatched_by_tag() {
    let mut s = fresh_session();
    let script = r#"
        graph-builder $h
        ^h "o" 1 "output" b-port
        ^h "src" b-node $_
        ^h "i" 1 "input" b-port
        ^h "snk" b-node $_
        ^h 0 0 1 0 b-wire
        ^h b-finish $g
        absent-slot $absent
        all-pure $ap
        ^g ^absent ^ap string-diagram $sd
        ^sd preview
    "#;
    let out = s.eval(script);
    assert!(out.contains("string-diagram"), "expected SD identification: {out}");
    // The slot summary should be visible — the all-pure sentinel
    // appears as a labelled slot rather than a hash.
    assert!(out.contains("all-pure"), "expected slot summary: {out}");
}

#[test]
fn preview_recognises_png_magic() {
    let mut s = fresh_session();
    // PNG signature + IHDR header for a 16×8 image.
    // IHDR is at offset 8: 4 bytes length + "IHDR" + 4 bytes width + 4 bytes height + ...
    let png = vec![
        0x89, 0x50, 0x4e, 0x47, 0x0d, 0x0a, 0x1a, 0x0a, // PNG magic
        0x00, 0x00, 0x00, 0x0d, b'I', b'H', b'D', b'R', // IHDR chunk length + tag
        0x00, 0x00, 0x00, 0x10, // width = 16
        0x00, 0x00, 0x00, 0x08, // height = 8
    ];
    let hex_str: String = png.iter().map(|b| format!("{b:02x}")).collect();
    let script = format!("\"{hex_str}\" hex store $h ^h preview");
    let out = s.eval(&script);
    assert!(out.contains("image/png"), "PNG should be detected: {out}");
    assert!(out.contains("16"), "PNG dims should include 16: {out}");
    assert!(out.contains("8"), "PNG dims should include 8: {out}");
}
