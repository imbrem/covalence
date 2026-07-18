---
name: web-server
description: Web server architecture and SvelteKit frontend details
disable-model-invocation: true
---

## Web server (`cov serve`)

```
cov serve [--port PORT] [--open] [--api] [--store [PATH]]
  → axum HTTP server on 127.0.0.1:PORT + Unix socket
  → serves embedded SvelteKit static files (rust-embed, requires "static" feature)
  → REST API (see below)
  → --api: serve API only, skip static frontend
  → --store: SQLite persistence
  → SPA fallback: unmatched routes serve index.html
```

`covalence-serve` features (all default):

- `static` — embeds SvelteKit build output via rust-embed; disable with `--no-default-features` to skip static assets entirely

The SvelteKit app uses `adapter-static` (pure SPA, `ssr = false`) so it compiles to plain HTML/JS/CSS that gets embedded into the Rust binary at compile time.

The frontend API base URL is configurable via `VITE_COV_API_BASE` (defaults to empty = same-origin). To host the static site separately (e.g. GitHub Pages) pointing at a remote backend:

```sh
VITE_COV_API_BASE=https://cov.example.com bun run build:web
```

## Covalence map

`apps/covalence-map/` is a separate semi-static knowledge and source browser.
`bun run dev:map` regenerates its data before starting the development server.
The data flow is:

```
tracked plaintext + source-local markers
  → target/covalence-notes.sqlite
  → fetched JSON indexes and per-file source shards
  → covalence-map
```

The SQLite database is the generated query layer, not authored truth, and JSON
is only interchange. `VITE_COVALENCE_MAP_DATA_BASE` can point the same frontend
at a future server-side JSON provider. Source content is not bundled into the
Svelte application; `/source?path=…#L…` provides stable line links.
