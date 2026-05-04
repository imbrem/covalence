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
            export PATH="$PWD/target/debug:$PATH"
            echo "covalence dev shell"
            echo "  cargo build --bin cog   build cog (available on PATH via target/debug)"
            echo "  bun run build           full build (wasm + esbuild)"
            echo "  bun run dev             dev server on localhost:3000"
          '';
        };
      }
    );
}
