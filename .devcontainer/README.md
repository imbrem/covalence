# Dev container (optional)

A reproducible covalence dev environment built on the repo's own
[`flake.nix`](../flake.nix), so the container and a native `nix develop` shell
are the **same** environment — one source of truth for the toolchain (Rust +
wasm targets, Bun, wasm-bindgen/binaryen, sccache, buck2/reindeer, Python +
maturin).

This is **opt-in and experimental**. Nothing in the normal build path needs it;
it exists so humans and agents can get a known-good `covalence` environment
without touching their host, and to play with a system-installed `cov` and
global caches in isolation.

## Use it

- **VS Code / Cursor:** "Dev Containers: Reopen in Container". On first create it
  builds the image and warms the flake devshell (`nix develop`), which downloads
  the toolchain once. `direnv` then auto-loads the flake env (the repo `.envrc`
  is `use flake`) on every shell.
- **CLI (devcontainer CLI):** `devcontainer up --workspace-folder .`

Once inside, everything in the top-level [`README.md`](../README.md) /
[`CLAUDE.md`](../CLAUDE.md) works as documented (`bun install`, `bun run build`,
`cargo test`, …).

## Notes

- The image is `nixos/nix:latest`; pin it to a specific tag for full
  reproducibility.
- The build cache toggle (`COV_CACHE`, default on → sccache) from the flake
  applies here too; sccache's object cache lives under `$HOME/.cache/sccache`.
- CI does **not** use this container yet — it installs tools directly (see
  `.github/workflows/ci.yml`). Cross-testing CI against the flake/devcontainer
  is future work (tracked in `notes/plans/next-stage.md`).
- Untested in the authoring environment (no Docker available there); if the
  image build needs a tweak, fix it here — the config is deliberately minimal.
