# Playwright e2e

Browser + API end-to-end tests for the covalence web app.

```sh
bun run build:serve   # prerequisite: builds the web bundle into target/debug/cov
bun run test:e2e      # run the functional specs
bun run bench:web     # run the latency benchmarks (not run by test:e2e)
```

## What runs where

| Path                     | Project    | Depends on                                     |
| ------------------------ | ---------- | ---------------------------------------------- |
| `specs/api.spec.ts`      | `chromium` | server only — must pass on any build           |
| `specs/repl.spec.ts`     | `chromium` | main-page testids (`repl-input`, `status-bar`) |
| `specs/lisp.spec.ts`     | `chromium` | /lisp testids (`help-widget`, `example-button`) |
| `specs/metamath.spec.ts` | `chromium` | /metamath heading + `/api/metamath/sessions`   |
| `bench.spec.ts`          | `bench`    | measurements only; run explicitly              |

Both scripts pass `--project`; a bare `playwright test --config
e2e/playwright.config.ts` runs the benchmarks too.

The UI specs assert against `data-testid` hooks and stable output text. Because
the binary embeds the web bundle at build time, a UI spec failing after a
frontend change usually means the bundle is stale — rebuild with
`bun run build:serve`.

## Server lifecycle

`global-setup.ts` spawns a prebuilt `target/debug/cov serve` on a free port
with `XDG_*` and `HOME` pointed at a temp dir (same isolation as
`tests/e2e.test.ts`), waits for `GET /api/health` to report `status: "ok"`, and
publishes the URL as `COV_E2E_URL`. `global-teardown.ts` kills that process
group and removes the temp dir.

## Running against a dev server

Set `COV_E2E_URL` and nothing is spawned or torn down:

```sh
cov serve --api            # terminal 1
bun run dev:web            # terminal 2 (Vite proxies /api to :3100)
COV_E2E_URL=http://localhost:5173 bun run test:e2e
```

Note that `api.spec.ts` talks to `COV_E2E_URL` directly, so the URL must be one
that serves `/api` — the Vite dev server does, via its proxy.

## Browsers

Playwright's bundled Chromium does not run on NixOS (missing shared
libraries). `playwright.config.ts` probes it and falls back to a system
chromium (`/run/current-system/sw/bin/chromium`, `/usr/bin/chromium`, …).
Override explicitly with `COV_E2E_CHROMIUM=/path/to/chrome`.
