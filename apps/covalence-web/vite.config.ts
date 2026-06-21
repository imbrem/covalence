import { sveltekit } from '@sveltejs/kit/vite';
import { createLogger, defineConfig } from 'vite';
import type { LogOptions, Plugin } from 'vite';
import { readdirSync, readFileSync } from 'node:fs';
import { join } from 'node:path';

// Filter the benign `node:async_hooks externalized for browser compatibility`
// warning emitted by vite:resolve. The references come from svelte's and
// SvelteKit's server-render code paths, which Vite's tree-shaker keeps in the
// client graph but never actually invokes at runtime.
const logger = createLogger();
const originalWarn = logger.warn;
logger.warn = (msg: string, options?: LogOptions) => {
	if (msg.includes('node:async_hooks') && msg.includes('externalized for browser compatibility')) {
		return;
	}
	originalWarn(msg, options);
};

// ---------------------------------------------------------------------------
// XDG discovery — mirrors covalence-proto/src/discovery
// ---------------------------------------------------------------------------

interface ServiceDescriptor {
	id: string;
	pid: number;
	version: string;
	started_at: string;
	socket: string | null;
	url: string | null;
	capabilities: string[];
	cwd: string;
}

/** Resolve $XDG_RUNTIME_DIR/covalence/registry, matching the Rust `dirs::runtime_dir()`. */
function registryDir(): string {
	const xdg = process.env.XDG_RUNTIME_DIR ?? '/tmp';
	return join(xdg, 'covalence', 'registry');
}

/** Check if a process is alive (POSIX kill(pid, 0)). */
function pidAlive(pid: number): boolean {
	try {
		process.kill(pid, 0);
		return true;
	} catch {
		return false;
	}
}

/**
 * Scan the XDG registry for live covalence servers.
 * Returns descriptors sorted by preference: cwd match first, then newest.
 */
function discoverServers(): ServiceDescriptor[] {
	const dir = registryDir();
	let entries: string[];
	try {
		entries = readdirSync(dir).filter((f) => f.endsWith('.json'));
	} catch {
		return [];
	}

	const cwd = process.cwd();
	const servers: ServiceDescriptor[] = [];

	for (const file of entries) {
		try {
			const raw = readFileSync(join(dir, file), 'utf-8');
			const desc: ServiceDescriptor = JSON.parse(raw);
			if (!pidAlive(desc.pid)) continue;
			servers.push(desc);
		} catch {
			continue;
		}
	}

	servers.sort((a, b) => {
		const aMatch = a.cwd === cwd;
		const bMatch = b.cwd === cwd;
		if (aMatch !== bMatch) return aMatch ? -1 : 1;
		return b.started_at.localeCompare(a.started_at);
	});

	return servers;
}

// ---------------------------------------------------------------------------
// Vite plugin: auto-detect covalence server
// ---------------------------------------------------------------------------

function covDiscovery(): Plugin {
	return {
		name: 'cov-discovery',
		configureServer(server) {
			const servers = discoverServers();
			if (servers.length === 0) {
				server.config.logger.warn(
					'\x1b[33m⚠ No running covalence server found.\x1b[0m\n' +
						'  Start one with: cov serve --api\n' +
						'  Or set COV_API to a remote URL.',
				);
			} else {
				const desc = servers[0];
				const cwdMatch = desc.cwd === process.cwd();
				server.config.logger.info(
					`\x1b[32m● Connected to covalence server\x1b[0m` +
						` v${desc.version} (pid ${desc.pid})` +
						(cwdMatch ? ' [cwd match]' : '') +
						` → ${desc.url ?? desc.socket}`,
				);
			}
		},
	};
}

// ---------------------------------------------------------------------------
// Config
// ---------------------------------------------------------------------------

/** Dev proxy target for /api requests.
 *  Priority: COV_API env → XDG registry auto-discovery → localhost:3100 fallback.
 */
function resolveApiTarget(): string {
	if (process.env.COV_API) return process.env.COV_API;

	const servers = discoverServers();
	if (servers.length > 0 && servers[0].url) return servers[0].url;

	return 'http://localhost:3100';
}

const apiTarget = resolveApiTarget();

export default defineConfig({
	customLogger: logger,
	plugins: [sveltekit(), covDiscovery()],
	// Web Workers (e.g. the kernel worker behind the `article` page) must be
	// bundled as ES modules — the production build is code-split, and Rollup
	// rejects the default `iife`/`umd` worker format for code-splitting builds.
	worker: {
		format: 'es',
	},
	server: {
		proxy: {
			'/api': {
				target: apiTarget,
				ws: true,
			},
		},
	},
});
