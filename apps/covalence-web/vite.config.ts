import { sveltekit } from '@sveltejs/kit/vite';
import { defineConfig } from 'vite';

/** Dev proxy target for /api requests. Override with COV_API env var.
 *  Examples:
 *    COV_API=http://localhost:8080 bun run dev:web
 *    COV_API=https://cov.example.com bun run dev:web
 */
const apiTarget = process.env.COV_API ?? 'http://localhost:3100';

export default defineConfig({
	plugins: [sveltekit()],
	server: {
		proxy: {
			'/api': apiTarget
		}
	}
});
