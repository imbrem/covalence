{
  description = "Covalence — theorem prover with Ion language tooling";

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
          extensions = [ "rustfmt" "clippy" ];
          targets = [
            "wasm32-wasip1-threads"
            "wasm32-unknown-unknown"
          ];
        };
      in
      {
        devShells.default = pkgs.mkShell {
          buildInputs = [
            rustToolchain
            pkgs.bun
            pkgs.wasm-pack
            pkgs.wasm-bindgen-cli
            pkgs.binaryen
            pkgs.esbuild
          ];

          shellHook = ''
            export PATH="$PWD/target/release:$PWD/target/debug:$PATH"
            mkdir -p target/release target/debug
            rm -f target/release/cog target/debug/cog
            printf '#!/bin/sh\nexec cov cog "$@"\n' > target/release/cog && chmod +x target/release/cog
            printf '#!/bin/sh\nexec cov cog "$@"\n' > target/debug/cog && chmod +x target/debug/cog
            echo "covalence dev shell"
            echo "  cargo build -p covalence --release   build cov (release, preferred on PATH)"
            echo "  cargo build -p covalence             build cov (debug, fallback on PATH)"
            echo "                                       'cog' is a wrapper that calls 'cov cog'"
            echo "  bun run build                        full build (native debug + wasm + esbuild)"
            echo "  bun run release                      full release build (native release + wasm + esbuild)"
            echo "  bun run code:browser                 build + launch web VSCode"
            echo "  bun run code:desktop                 build + launch desktop VSCode"
          '';
        };
      }
    );
}
