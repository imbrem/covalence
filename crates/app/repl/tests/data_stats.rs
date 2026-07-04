//! Integration tests for the `arrow-stats`, `parquet-stats`, and
//! `parquet-stats-tree` REPL commands.
#![cfg(all(feature = "arrow", feature = "parquet"))]

use std::sync::Arc;

use covalence_arrow::arrow::array::Int32Array;
use covalence_arrow::arrow::datatypes::{DataType, Field, Schema};
use covalence_arrow::arrow::ipc::writer::FileWriter;
use covalence_arrow::arrow::record_batch::RecordBatch;
use covalence_hash::O256;
use covalence_object::{DirBuilder, DirMode, TableBuilder};
use covalence_repl::{Session, SyncBackend};
use covalence_shell::Kernel;
use covalence_parquet::parquet::arrow::ArrowWriter;
use covalence_parquet::parquet::file::properties::WriterProperties;

fn arrow_ipc_blob(rows: &[i32]) -> Vec<u8> {
    let schema = Arc::new(Schema::new(vec![Field::new("v", DataType::Int32, false)]));
    let batch = RecordBatch::try_new(
        schema.clone(),
        vec![Arc::new(Int32Array::from(rows.to_vec()))],
    )
    .unwrap();
    let mut buf = Vec::new();
    {
        let mut w = FileWriter::try_new(&mut buf, &schema).unwrap();
        w.write(&batch).unwrap();
        w.finish().unwrap();
    }
    buf
}

fn parquet_blob(rows: &[i32]) -> Vec<u8> {
    let schema = Arc::new(Schema::new(vec![Field::new("v", DataType::Int32, false)]));
    let batch = RecordBatch::try_new(
        schema.clone(),
        vec![Arc::new(Int32Array::from(rows.to_vec()))],
    )
    .unwrap();
    let mut buf = Vec::new();
    {
        let mut w = ArrowWriter::try_new(&mut buf, schema, Some(WriterProperties::new())).unwrap();
        w.write(&batch).unwrap();
        w.close().unwrap();
    }
    buf
}

#[test]
fn arrow_stats_command() {
    let kernel = Kernel::new();
    let hash = kernel.store_blob(&arrow_ipc_blob(&[1, 2, 3, 4])).unwrap();

    let mut session = Session::new(Box::new(kernel), false, false);
    let out = session.eval(&format!("{hash} arrow-stats"));
    assert!(out.contains("arrow (file)"), "got: {out}");
    assert!(out.contains("4 rows"), "got: {out}");
    assert!(out.contains("v: Int32"), "got: {out}");
}

#[test]
fn parquet_stats_command() {
    let kernel = Kernel::new();
    let hash = kernel.store_blob(&parquet_blob(&[10, 20, 30])).unwrap();

    let mut session = Session::new(Box::new(kernel), false, false);
    let out = session.eval(&format!("{hash} parquet-stats"));
    assert!(out.contains("parquet:"), "got: {out}");
    assert!(out.contains("1 file(s)"), "got: {out}");
    assert!(out.contains("3 rows"), "got: {out}");
}

#[test]
fn parquet_stats_auto_detects_hive_tree() {
    // Tree:
    //   year=2024/
    //     month=01/data.parquet  (rows = [1,2])
    //     month=02/data.parquet  (rows = [3,4,5])
    let kernel = Kernel::new();

    let leaf_a = kernel.store_blob(&parquet_blob(&[1, 2])).unwrap();
    let leaf_b = kernel.store_blob(&parquet_blob(&[3, 4, 5])).unwrap();

    let month_01 = {
        let mut b = DirBuilder::new();
        b.entry("data.parquet", DirMode::REGULAR, leaf_a);
        store_dir(&kernel, &b)
    };
    let month_02 = {
        let mut b = DirBuilder::new();
        b.entry("data.parquet", DirMode::REGULAR, leaf_b);
        store_dir(&kernel, &b)
    };
    let year = {
        let mut b = DirBuilder::new();
        b.entry("month=01", DirMode::DIR, month_01);
        b.entry("month=02", DirMode::DIR, month_02);
        store_dir(&kernel, &b)
    };
    let root = {
        let mut b = DirBuilder::new();
        b.entry("year=2024", DirMode::DIR, year);
        store_dir(&kernel, &b)
    };

    let mut session = Session::new(Box::new(kernel), false, false);
    let out = session.eval(&format!("{root} parquet-stats"));
    assert!(out.contains("2 file(s)"), "got: {out}");
    assert!(out.contains("5 rows"), "got: {out}");
    assert!(out.contains("partitions: year, month"), "got: {out}");
}

/// Build a `Dir` table from a builder, store it via `store_tree`, return its hash.
fn store_dir(kernel: &Kernel, b: &DirBuilder<'_>) -> O256 {
    let mut tb = TableBuilder::new(covalence_object::Dir);
    for row in b.iter() {
        tb.push_row(covalence_object::DirRow {
            name: row.name.as_bytes().to_vec(),
            mode: row.mode,
            child: row.child,
        });
    }
    let table = tb.build();
    kernel.store_tree(table.as_bytes()).unwrap()
}
