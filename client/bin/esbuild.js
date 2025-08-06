/*---------------------------------------------------------------------------------------------
 *  Copyright (c) Microsoft Corporation. All rights reserved.
 *  Licensed under the MIT License. See License.txt in the project root for license information.
 *--------------------------------------------------------------------------------------------*/
//@ts-check
const esbuild = require('esbuild');
const path = require('path');
const fs = require('fs');

/**
 * Return the absolute path of <pkgName>'s root directory.
 * @param {string} pkgName  npm specifier, e.g. "vscode-languageclient"
 * @param {string[]} [search] additional search dirs (same as {paths: [...]})
 */
function resolvePackageRoot(pkgName, search = []) {
  // 1. Let Node give us *one* file inside the package (normally its main entry):
  const entry = require.resolve(pkgName, { paths: search });

  // 2. Walk up until we find the package.json that belongs to that package
  let dir = path.dirname(entry);
  while (!fs.existsSync(path.join(dir, 'package.json'))) {
	const parent = path.dirname(dir);
	if (parent === dir) {
	  throw new Error(`Could not find package.json for ${pkgName}`);
	}
	dir = parent;
  }
  return dir;                    // ← the package root
}

/**
 * @typedef {import('esbuild').BuildOptions} BuildOptions
 */

/** @type BuildOptions */
const sharedWebOptions = {
	bundle: true,
	external: ['vscode'],
	target: 'es2020',
	platform: 'browser',
	alias: {
		'vscode-languageclient/node': resolvePackageRoot('vscode-languageclient', ["./client"]) + "/lib/browser/main.js",
	},
	sourcemap: true,
};

/** @type BuildOptions */
const webOptions = {
	entryPoints: ['src/extension.ts'],
	outfile: 'dist/web/extension.js',
	format: 'cjs',
	...sharedWebOptions,
};

/** @type BuildOptions */
const sharedDesktopOptions = {
	bundle: true,
	external: ['vscode'],
	target: 'es2020',
	platform: 'node',
	sourcemap: true,
};

/** @type BuildOptions */
const desktopOptions = {
	entryPoints: ['src/extension.ts'],
	outfile: 'dist/desktop/extension.js',
	format: 'cjs',
	...sharedDesktopOptions,
};

function createContexts() {
	return Promise.all([
		esbuild.context(webOptions),
		esbuild.context(desktopOptions),
	]);
}

createContexts().then(contexts => {
	if (process.argv[2] === '--watch') {
		const promises = [];
		for (const context of contexts) {
			promises.push(context.watch());
		}
		return Promise.all(promises).then(() => { return undefined; });
	} else {
		const promises = [];
		for (const context of contexts) {
			promises.push(context.rebuild());
		}
		Promise.all(promises).then(async () => {
			for (const context of contexts) {
				await context.dispose();
			}
		}).then(() => { return undefined; }).catch(console.error);
	}
}).catch(console.error);