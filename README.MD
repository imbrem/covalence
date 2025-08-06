# Covalence

An experimental theorem prover for extensional MLTT, developed as a VSCode extension.

Formalization and documentation of the underlying theory can be found in the
[covalence-lean](https://github.com/imbrem/covalence-lean) repository.

## Getting Started

Requirements:
- `bun`
- Rust toolchain

Instructions:
- Clone the repository
- Run `bun install`
- To develop locally: open the repo in VSCode, and press `F5`
- To run in a browser: 
    - Build with `bun run build`
    - Open with `bun run browser`
- To run in [`vscode.dev`](https://vscode.dev/) or [`insiders.vscode.dev`](https://insiders.vscode.dev):
    - Follow the instructions
      [here](https://code.visualstudio.com/api/extension-guides/web-extensions#test-your-web-extension-in-vscode.dev)
      to generate the necessary certificate to side-load the extension
    - Build with `bun run build`
    - Serve with `bun run serve`
    - Install with "Developer: Install Extension from Location" (push `Ctrl+P` in the VSCode window
      and type) with location `https://localhost:5000`

You can also:
- Run tests for all Rust modules with `cargo test`
- Generate documentation with `bun run doc`; open with `bun run view-docs`