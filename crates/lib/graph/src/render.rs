//! SVG renderer for a [`ResolvedDiagram`].
//!
//! Top-to-bottom layout: node `i` sits in row `i`. Data inputs are
//! distributed on the top edge, outputs on the bottom edge, with the
//! leftmost slot reserved for the "state thread" port on ordered
//! nodes. The state thread is drawn as a dashed red wire connecting
//! consecutive ordered nodes (with a stub above the first and below
//! the last).
//!
//! Layout knobs live in [`LayoutOpts`] and are stable; the SVG markup
//! itself is an internal implementation detail.

use std::fmt::Write;

use crate::canonical::{Graph, PortKind};
use crate::overlay::NodeKind;
use crate::string_diagram::ResolvedDiagram;

#[derive(Clone, Debug)]
pub struct LayoutOpts {
    pub box_w: f32,
    pub box_h: f32,
    pub data_port_min_sep: f32,
    pub row_h: f32,
    pub margin_x: f32,
    pub margin_y: f32,
    pub state_stub_len: f32,
    pub state_slot_pad: f32,
}

impl Default for LayoutOpts {
    fn default() -> Self {
        Self {
            box_w: 180.0,
            box_h: 50.0,
            data_port_min_sep: 36.0,
            row_h: 130.0,
            margin_x: 60.0,
            margin_y: 60.0,
            state_stub_len: 36.0,
            state_slot_pad: 22.0,
        }
    }
}

#[derive(Clone, Debug)]
struct NodeBox {
    x: f32,
    y: f32,
    w: f32,
    h: f32,
    inputs: Vec<PortAnchor>,
    outputs: Vec<PortAnchor>,
    state_in: Option<(f32, f32)>,
    state_out: Option<(f32, f32)>,
    kind: NodeKind,
    label: String,
}

#[derive(Clone, Debug)]
struct PortAnchor {
    port_idx: u32,
    x: f32,
    y: f32,
    name: String,
    type_id: u64,
}

#[derive(Clone, Debug)]
struct LaidOut {
    boxes: Vec<NodeBox>,
    width: f32,
    height: f32,
    state_segments: Vec<StateSeg>,
}

#[derive(Copy, Clone, Debug)]
struct StateSeg {
    from: (f32, f32),
    to: (f32, f32),
}

fn layout<P: AsRef<[u8]>>(diagram: &ResolvedDiagram<P>, opts: &LayoutOpts) -> LaidOut {
    let graph: &Graph<P> = diagram.graph;
    let mut boxes = Vec::with_capacity(graph.node_count() as usize);
    for (i, node) in graph.nodes().iter().enumerate() {
        let inputs_n = node
            .ports
            .iter()
            .filter(|p| p.kind == PortKind::Input)
            .count();
        let outputs_n = node
            .ports
            .iter()
            .filter(|p| p.kind == PortKind::Output)
            .count();
        let kind = diagram.kind_of(i as u32);
        let is_ordered = kind.is_ordered();

        let data_port_count = inputs_n.max(outputs_n).max(1) as f32;
        let data_area_min = data_port_count * opts.data_port_min_sep + 32.0;
        let base_w = if is_ordered {
            data_area_min + opts.state_slot_pad
        } else {
            data_area_min
        };
        let w = opts.box_w.max(base_w);
        let h = opts.box_h;

        let x = opts.margin_x;
        let y = opts.margin_y + i as f32 * opts.row_h;
        let data_left_edge = if is_ordered {
            x + opts.state_slot_pad
        } else {
            x
        };
        let data_area_w = w - if is_ordered { opts.state_slot_pad } else { 0.0 };

        let state_in = if is_ordered {
            Some((x + opts.state_slot_pad / 2.0, y))
        } else {
            None
        };
        let state_out = if is_ordered {
            Some((x + opts.state_slot_pad / 2.0, y + h))
        } else {
            None
        };

        let mut inputs = Vec::with_capacity(inputs_n);
        let mut outputs = Vec::with_capacity(outputs_n);
        let mut in_i = 0usize;
        let mut out_i = 0usize;
        for (pi, port) in node.ports.iter().enumerate() {
            match port.kind {
                PortKind::Input => {
                    let slot = (in_i + 1) as f32 / (inputs_n + 1) as f32;
                    inputs.push(PortAnchor {
                        port_idx: pi as u32,
                        x: data_left_edge + slot * data_area_w,
                        y,
                        name: port.name.clone(),
                        type_id: port.type_id.0,
                    });
                    in_i += 1;
                }
                PortKind::Output => {
                    let slot = (out_i + 1) as f32 / (outputs_n + 1) as f32;
                    outputs.push(PortAnchor {
                        port_idx: pi as u32,
                        x: data_left_edge + slot * data_area_w,
                        y: y + h,
                        name: port.name.clone(),
                        type_id: port.type_id.0,
                    });
                    out_i += 1;
                }
            }
        }

        boxes.push(NodeBox {
            x,
            y,
            w,
            h,
            inputs,
            outputs,
            state_in,
            state_out,
            kind,
            label: diagram.label_for(i as u32),
        });
    }

    let mut ordered_ids: Vec<usize> = Vec::new();
    for (i, b) in boxes.iter().enumerate() {
        if b.kind.is_ordered() {
            ordered_ids.push(i);
        }
    }
    let mut state_segments = Vec::new();
    if let Some(&first) = ordered_ids.first()
        && let Some(p) = boxes[first].state_in
    {
        state_segments.push(StateSeg {
            from: (p.0, p.1 - opts.state_stub_len),
            to: p,
        });
    }
    for pair in ordered_ids.windows(2) {
        let a = &boxes[pair[0]];
        let b = &boxes[pair[1]];
        if let (Some(ao), Some(bi)) = (a.state_out, b.state_in) {
            state_segments.push(StateSeg { from: ao, to: bi });
        }
    }
    if let Some(&last) = ordered_ids.last()
        && let Some(p) = boxes[last].state_out
    {
        state_segments.push(StateSeg {
            from: p,
            to: (p.0, p.1 + opts.state_stub_len),
        });
    }

    let max_w = boxes.iter().map(|b| b.w).fold(opts.box_w, f32::max);
    let width = opts.margin_x * 2.0 + max_w;
    let last_h = boxes.last().map(|b| b.h).unwrap_or(0.0);
    let height = if boxes.is_empty() {
        opts.margin_y * 2.0
    } else {
        opts.margin_y * 2.0 + (boxes.len() - 1) as f32 * opts.row_h + last_h
    };
    LaidOut {
        boxes,
        width,
        height,
        state_segments,
    }
}

/// Render a string diagram to standalone SVG markup.
///
/// The emitted SVG is intentionally minimal: structural `<g>` groups
/// carry `data-node-id`, `data-port-idx`, and `data-type-id` attributes
/// so an interactive embedder can attach behaviour without re-parsing.
pub fn render_svg<P: AsRef<[u8]>>(diagram: &ResolvedDiagram<P>, opts: &LayoutOpts) -> String {
    let l = layout(diagram, opts);
    let mut s = String::with_capacity(2048);
    let _ = write!(
        s,
        "<svg xmlns=\"http://www.w3.org/2000/svg\" viewBox=\"0 0 {w} {h}\" \
         width=\"{w}\" height=\"{h}\" font-family=\"ui-monospace, monospace\" font-size=\"12\">",
        w = l.width,
        h = l.height,
    );

    // Data edges first so they sit beneath node boxes.
    s.push_str("<g class=\"edges\" stroke=\"#1c2233\" fill=\"none\" stroke-width=\"1.5\">");
    let graph: &Graph<P> = diagram.graph;
    for e in graph.edges() {
        let from_box = &l.boxes[e.from_node.0 as usize];
        let to_box = &l.boxes[e.to_node.0 as usize];
        let from = from_box
            .outputs
            .iter()
            .find(|a| a.port_idx == e.from_port.0)
            .map(|a| (a.x, a.y));
        let to = to_box
            .inputs
            .iter()
            .find(|a| a.port_idx == e.to_port.0)
            .map(|a| (a.x, a.y));
        if let (Some(p1), Some(p2)) = (from, to) {
            write_bezier(&mut s, p1, p2);
        }
    }
    s.push_str("</g>");

    // State thread (dashed red).
    s.push_str(
        "<g class=\"state-thread\" stroke=\"#c43030\" stroke-width=\"1.5\" \
         stroke-dasharray=\"5 4\" fill=\"none\">",
    );
    for seg in &l.state_segments {
        write_bezier(&mut s, seg.from, seg.to);
    }
    s.push_str("</g>");

    // Node boxes + ports + labels.
    s.push_str("<g class=\"nodes\">");
    for (i, b) in l.boxes.iter().enumerate() {
        let _ = write!(
            s,
            "<g class=\"node {kc}\" data-node-id=\"{i}\">",
            kc = if b.kind.is_ordered() {
                "ordered"
            } else {
                "pure"
            },
        );
        let _ = write!(
            s,
            "<rect x=\"{x}\" y=\"{y}\" width=\"{w}\" height=\"{h}\" rx=\"4\" ry=\"4\" \
             fill=\"#ffffff\" stroke=\"#1c2233\" stroke-width=\"1.25\"/>",
            x = b.x,
            y = b.y,
            w = b.w,
            h = b.h,
        );
        let cx = b.x + b.w / 2.0;
        let cy = b.y + b.h / 2.0 + 4.0;
        let _ = write!(
            s,
            "<text x=\"{cx}\" y=\"{cy}\" text-anchor=\"middle\" fill=\"#1c2233\">{label}</text>",
            label = escape_xml(&b.label),
        );
        for p in &b.inputs {
            write_port(&mut s, p, "input");
        }
        for p in &b.outputs {
            write_port(&mut s, p, "output");
        }
        if let Some((sx, sy)) = b.state_in {
            let _ = write!(
                s,
                "<circle cx=\"{sx}\" cy=\"{sy}\" r=\"3.5\" fill=\"#ffffff\" \
                 stroke=\"#c43030\" stroke-width=\"1.5\" stroke-dasharray=\"2 2\">\
                 <title>state in</title></circle>",
            );
        }
        if let Some((sx, sy)) = b.state_out {
            let _ = write!(
                s,
                "<circle cx=\"{sx}\" cy=\"{sy}\" r=\"3.5\" fill=\"#ffffff\" \
                 stroke=\"#c43030\" stroke-width=\"1.5\" stroke-dasharray=\"2 2\">\
                 <title>state out</title></circle>",
            );
        }
        s.push_str("</g>");
    }
    s.push_str("</g>");
    s.push_str("</svg>");
    s
}

fn write_port(s: &mut String, p: &PortAnchor, kind: &str) {
    let _ = write!(
        s,
        "<circle cx=\"{cx}\" cy=\"{cy}\" r=\"4\" fill=\"#1c2233\" \
         data-port-idx=\"{idx}\" data-type-id=\"{ty}\">\
         <title>{kind} {name} : type {ty}</title></circle>",
        cx = p.x,
        cy = p.y,
        idx = p.port_idx,
        ty = p.type_id,
        name = escape_xml(&p.name),
    );
}

fn write_bezier(s: &mut String, p1: (f32, f32), p2: (f32, f32)) {
    let dy = (p2.1 - p1.1).abs().max(20.0);
    let curve = dy * 0.4;
    let c1 = (p1.0, p1.1 + curve);
    let c2 = (p2.0, p2.1 - curve);
    let _ = write!(
        s,
        "<path d=\"M{x1},{y1} C{cx1},{cy1} {cx2},{cy2} {x2},{y2}\"/>",
        x1 = p1.0,
        y1 = p1.1,
        cx1 = c1.0,
        cy1 = c1.1,
        cx2 = c2.0,
        cy2 = c2.1,
        x2 = p2.0,
        y2 = p2.1,
    );
}

// ----------------------------------------------------------------------
// Plain DAG renderer (no labels, no per-node Pure/Ordered overlays —
// just dots and lines). Use this for raw `COVG` blobs.
// ----------------------------------------------------------------------

/// Layout knobs for the DAG renderer. Independent from [`LayoutOpts`]
/// because the DAG view is meant to be more compact.
#[derive(Clone, Debug)]
pub struct DagLayoutOpts {
    pub dot_radius: f32,
    pub row_h: f32,
    pub col_x: f32,
    pub margin_y: f32,
}

impl Default for DagLayoutOpts {
    fn default() -> Self {
        Self {
            dot_radius: 7.0,
            row_h: 90.0,
            col_x: 60.0,
            margin_y: 40.0,
        }
    }
}

/// Render a graph as a plain layered DAG: small filled circles
/// distributed by topological rank, with smoothstep-style edges
/// between them. Multi-edges between the same node pair are collapsed
/// into a single visible line, matching the frontend
/// `GraphDagView` aesthetic.
pub fn render_dag_svg<P: AsRef<[u8]>>(graph: &Graph<P>, opts: &DagLayoutOpts) -> String {
    let n = graph.node_count() as usize;
    let (ranks, _max_rank) = topo_ranks(graph);
    // Group nodes per rank, preserving insertion order within each rank.
    let mut by_rank: std::collections::BTreeMap<u32, Vec<usize>> =
        std::collections::BTreeMap::new();
    for (i, &r) in ranks.iter().enumerate() {
        by_rank.entry(r).or_default().push(i);
    }
    let col_w = opts.row_h * 0.7; // horizontal spacing between siblings
    let center_x = opts.col_x + col_w * 2.0;
    let dot_centers: Vec<(f32, f32)> = {
        let mut centers = vec![(0.0_f32, 0.0_f32); n];
        for (rank, ids) in &by_rank {
            let total_w = (ids.len().saturating_sub(1)) as f32 * col_w;
            let start_x = center_x - total_w / 2.0;
            let y = opts.margin_y + (*rank as f32) * opts.row_h;
            for (i, &node) in ids.iter().enumerate() {
                centers[node] = (start_x + i as f32 * col_w, y);
            }
        }
        centers
    };

    // Distinct edges by (from_node, to_node). Order preserved.
    let mut seen = std::collections::HashSet::new();
    let mut distinct: Vec<(u32, u32)> = Vec::new();
    for e in graph.edges() {
        let key = (e.from_node.0, e.to_node.0);
        if seen.insert(key) {
            distinct.push(key);
        }
    }

    // SVG dimensions: tight bounding box around the laid-out dots.
    let (min_x, max_x) = dot_centers
        .iter()
        .fold((f32::INFINITY, f32::NEG_INFINITY), |(mn, mx), &(x, _)| {
            (mn.min(x), mx.max(x))
        });
    let max_y = dot_centers.iter().fold(0f32, |m, &(_, y)| m.max(y));
    let pad = opts.col_x;
    let (width, height) = if n == 0 {
        (pad * 2.0, opts.margin_y * 2.0)
    } else {
        (max_x - min_x + pad * 2.0, max_y + pad)
    };
    // Shift coordinates so the leftmost dot has positive x with padding.
    let x_shift = if n == 0 { 0.0 } else { pad - min_x };
    let dot_centers: Vec<(f32, f32)> = dot_centers
        .into_iter()
        .map(|(x, y)| (x + x_shift, y))
        .collect();

    let mut s = String::with_capacity(512 + n * 80 + distinct.len() * 80);
    let _ = write!(
        s,
        "<svg xmlns=\"http://www.w3.org/2000/svg\" viewBox=\"0 0 {w} {h}\" \
         width=\"{w}\" height=\"{h}\" font-family=\"ui-monospace, monospace\" font-size=\"10\">",
        w = width,
        h = height,
    );

    s.push_str("<g class=\"edges\" stroke=\"#1c2233\" fill=\"none\" stroke-width=\"1.5\">");
    for (from, to) in distinct.iter() {
        let p1 = dot_centers[*from as usize];
        let p2 = dot_centers[*to as usize];
        write_smoothstep(&mut s, p1, p2);
    }
    s.push_str("</g>");

    s.push_str("<g class=\"nodes\">");
    for (i, (cx, cy)) in dot_centers.iter().enumerate() {
        let inputs = graph.nodes()[i]
            .ports
            .iter()
            .filter(|p| p.kind == PortKind::Input)
            .count();
        let outputs = graph.nodes()[i]
            .ports
            .iter()
            .filter(|p| p.kind == PortKind::Output)
            .count();
        let _ = write!(
            s,
            "<g class=\"node\" data-node-id=\"{i}\">\
             <circle cx=\"{cx}\" cy=\"{cy}\" r=\"{r}\" fill=\"#1c2233\" stroke=\"#1c2233\">\
             <title>#{i} (in:{inputs} out:{outputs})</title></circle>\
             <text x=\"{tx}\" y=\"{ty}\" text-anchor=\"middle\" fill=\"#ffffff\" font-size=\"9\">{i}</text>\
             </g>",
            r = opts.dot_radius,
            tx = cx,
            ty = cy + 3.0,
        );
    }
    s.push_str("</g>");
    s.push_str("</svg>");
    s
}

/// Longest-path rank for each node via Kahn's algorithm. Returns the
/// rank vector plus the maximum rank reached. Nodes unreachable from
/// any source (cycles) are placed one rank below everything else, in
/// insertion order.
fn topo_ranks<P>(graph: &Graph<P>) -> (Vec<u32>, u32) {
    let n = graph.node_count() as usize;
    let mut in_deg = vec![0u32; n];
    let mut succ: Vec<Vec<u32>> = vec![Vec::new(); n];
    for e in graph.edges() {
        if e.from_node.0 == e.to_node.0 {
            continue;
        }
        succ[e.from_node.0 as usize].push(e.to_node.0);
        in_deg[e.to_node.0 as usize] += 1;
    }
    let mut rank = vec![0u32; n];
    let mut remaining = in_deg.clone();
    let mut queue: std::collections::VecDeque<u32> = (0..n as u32)
        .filter(|&i| remaining[i as usize] == 0)
        .collect();
    while let Some(v) = queue.pop_front() {
        for &u in &succ[v as usize] {
            let candidate = rank[v as usize] + 1;
            if rank[u as usize] < candidate {
                rank[u as usize] = candidate;
            }
            remaining[u as usize] -= 1;
            if remaining[u as usize] == 0 {
                queue.push_back(u);
            }
        }
    }
    let mut max_rank = rank.iter().copied().max().unwrap_or(0);
    for (i, &rem) in remaining.iter().enumerate() {
        if rem > 0 {
            max_rank += 1;
            rank[i] = max_rank;
        }
    }
    (rank, max_rank)
}

/// Smoothstep SVG path between two points: vertical from source,
/// short horizontal to align columns, vertical to target. Matches the
/// frontend Svelte Flow `smoothstep` edge type.
fn write_smoothstep(s: &mut String, p1: (f32, f32), p2: (f32, f32)) {
    let mid_y = (p1.1 + p2.1) / 2.0;
    let _ = write!(
        s,
        "<path d=\"M{x1},{y1} L{x1},{my} L{x2},{my} L{x2},{y2}\"/>",
        x1 = p1.0,
        y1 = p1.1,
        x2 = p2.0,
        y2 = p2.1,
        my = mid_y,
    );
}

fn escape_xml(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    for c in s.chars() {
        match c {
            '<' => out.push_str("&lt;"),
            '>' => out.push_str("&gt;"),
            '&' => out.push_str("&amp;"),
            '"' => out.push_str("&quot;"),
            '\'' => out.push_str("&apos;"),
            _ => out.push(c),
        }
    }
    out
}
