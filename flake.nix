{
  description = "Covalence — LCF-style theorem prover using WASM components";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    rust-overlay = {
      url = "github:oxalica/rust-overlay";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, rust-overlay, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        overlays = [ (import rust-overlay) ];
        pkgs = import nixpkgs { inherit system overlays; };

        rustToolchain = pkgs.rust-bin.stable.latest.default.override {
          extensions = [ "rust-src" "rust-analyzer" "rustfmt" "clippy" ];
          targets = [
            "wasm32-wasip1-threads"
            "wasm32-unknown-unknown"
          ];
        };

        python = pkgs.python3.withPackages (ps: [
          ps.pytest
        ]);
      in
      {
        devShells.default = pkgs.mkShell {
          buildInputs = [
            rustToolchain
            pkgs.bashInteractive
            pkgs.bun
            pkgs.wasm-pack
            pkgs.wasm-bindgen-cli
            pkgs.binaryen
            pkgs.esbuild
            pkgs.cargo-nextest
            pkgs.graphviz # `dot` — renders docs/deps/graph.svg (bun run deps)

            # Shared cross-worktree build cache (see shellHook: COV_CACHE toggle).
            pkgs.sccache

            # Buck2 experiment (see notes/vibes/build/buck2-experiment.md). cargo
            # remains the source of truth; these drive the third-party/leaf slice.
            pkgs.buck2
            pkgs.reindeer

            # Python bindings
            python
            pkgs.maturin
          ];

          shellHook = ''
            export SHELL="${pkgs.bashInteractive}/bin/bash"
            export PATH="$PWD/target/release:$PWD/target/debug:$PATH"
            mkdir -p target/release target/debug
            rm -f target/release/cog target/debug/cog
            printf '#!/bin/sh\nexec cov cog "$@"\n' > target/release/cog && chmod +x target/release/cog
            printf '#!/bin/sh\nexec cov cog "$@"\n' > target/debug/cog && chmod +x target/debug/cog

            # Cross-worktree build cache. sccache's object cache lives in
            # $SCCACHE_DIR (default ~/.cache/sccache) — OUTSIDE any single
            # checkout — so a fresh git worktree reuses the dependency crates
            # already compiled elsewhere instead of rebuilding the world. The
            # trade-off is no rustc incremental (sccache can't cache it), so the
            # inner edit-loop of one crate is a touch slower. Default on; set
            # COV_CACHE=off for pure local incremental builds.
            if [ "''${COV_CACHE:-on}" != "off" ]; then
              export RUSTC_WRAPPER="${pkgs.sccache}/bin/sccache"
              export CARGO_INCREMENTAL=0
              export SCCACHE_DIR="''${SCCACHE_DIR:-$HOME/.cache/sccache}"
            fi

            echo "covalence dev shell"
            echo "  cargo build -p covalence --release   build cov (release, preferred on PATH)"
            echo "  cargo build -p covalence             build cov (debug, fallback on PATH)"
            echo "                                       'cog' is a wrapper that calls 'cov cog'"
            echo "  bun run build                        full build (native debug + wasm + esbuild)"
            echo "  bun run release                      full release build (native release + wasm + esbuild)"
            echo "  bun run code:browser                 build + launch web VSCode"
            echo "  bun run code:desktop                 build + launch desktop VSCode"
            echo ""
            echo "  cd crates/ffi/python"
            echo "  maturin develop                      build Python bindings (editable)"
            echo "  pytest tests/                        run Python tests"
            echo ""
            if [ "''${COV_CACHE:-on}" != "off" ]; then
              echo "  build cache: sccache ON (shared $SCCACHE_DIR; COV_CACHE=off to disable)"
            else
              echo "  build cache: sccache OFF (local incremental; unset COV_CACHE to share)"
            fi
          '';
        };
      }
    );
}
