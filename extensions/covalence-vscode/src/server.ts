import {
  type ExtensionContext,
  type OutputChannel,
  UIKind,
  Uri,
  env,
  workspace,
} from "vscode";
import {
  LanguageClient,
  type LanguageClientOptions,
  type ServerOptions,
  TransportKind,
} from "vscode-languageclient/node";
import { Wasm, type ProcessOptions } from "@vscode/wasm-wasi/v1";
import {
  createStdioOptions,
  createUriConverters,
  startServer,
} from "@vscode/wasm-wasi-lsp";

export type LspMode = "native" | "wasm";

export interface LspServer {
  client: LanguageClient;
  /** Convert a VSCode URI to the filesystem path the LSP server sees. */
  toServerPath: (uri: Uri) => string;
  mode: LspMode;
  /** Human-readable description of what was launched (e.g. "native cov 0.1.0" or "wasm"). */
  description: string;
}

interface NativeBinary {
  command: string;
  version: string;
}

/** Resolve `${workspaceFolder}` in a setting value. */
function resolveSettingPath(raw: string): string {
  const folders = workspace.workspaceFolders;
  if (folders?.length) {
    return raw.replace(/\$\{workspaceFolder\}/g, folders[0].uri.fsPath);
  }
  return raw;
}

/** Probe a candidate binary by running `<cmd> lsp --version`. */
function probeBinary(
  command: string,
  channel: OutputChannel,
): Promise<NativeBinary | null> {
  const cp: typeof import("child_process") = require("child_process");
  return new Promise((resolve) => {
    cp.execFile(
      command,
      ["lsp", "--version"],
      { timeout: 5000 },
      (err, stdout) => {
        if (err) {
          channel.appendLine(
            `Native detection: ${command} failed (${err.message})`,
          );
          resolve(null);
        } else {
          channel.appendLine(`Native detection: found ${stdout.trim()}`);
          resolve({ command, version: stdout.trim() });
        }
      },
    );
  });
}

/**
 * Try to find a native `cov` binary.
 *
 * Resolution order:
 * 1. `covalence.server.path` setting (if set)
 * 2. `cov` on PATH (Linux desktop only)
 * 3. null → WASM fallback
 */
async function findNativeBinary(
  channel: OutputChannel,
): Promise<NativeBinary | null> {
  if (env.uiKind === UIKind.Web) {
    channel.appendLine("Native detection: skipped (web environment)");
    return null;
  }

  // 1. User-configured path takes priority
  const configured = workspace
    .getConfiguration("covalence")
    .get<string>("server.path");
  if (configured) {
    const resolved = resolveSettingPath(configured);
    channel.appendLine(`Native detection: trying configured path: ${resolved}`);
    return probeBinary(resolved, channel);
  }

  // 2. PATH lookup (Linux only for now)
  // TODO: enable macOS once tested
  if (process.platform !== "linux") {
    channel.appendLine(
      `Native detection: skipped (platform: ${process.platform})`,
    );
    return null;
  }

  return probeBinary("cov", channel);
}

function fileUriToPath(uri: string): string {
  return decodeURIComponent(uri.replace(/^file:\/\//, ""));
}

export async function createLspServer(opts: {
  context: ExtensionContext;
  channel: OutputChannel;
  documentSelector: LanguageClientOptions["documentSelector"];
}): Promise<LspServer> {
  const { context, channel, documentSelector } = opts;
  const nativeBinary = await findNativeBinary(channel);

  // --- Native path ---
  if (nativeBinary) {
    const serverOptions: ServerOptions = {
      command: nativeBinary.command,
      args: ["lsp"],
      transport: TransportKind.stdio,
    };
    const clientOptions: LanguageClientOptions = {
      documentSelector,
      outputChannel: channel,
    };
    return {
      client: new LanguageClient(
        "covalence-lsp",
        "Covalence LSP",
        serverOptions,
        clientOptions,
      ),
      toServerPath: (uri) => uri.fsPath,
      mode: "native",
      description: `native ${nativeBinary.version}`,
    };
  }

  // --- WASM fallback ---
  const wasm: Wasm = await Wasm.load();
  const uriConverters = createUriConverters()!;

  const serverOptions: ServerOptions = async () => {
    const options: ProcessOptions = {
      stdio: createStdioOptions(),
      mountPoints: [{ kind: "workspaceFolder" }],
      args: ["lsp", "--vscode"],
    };

    const filename = Uri.joinPath(context.extensionUri, "dist", "cov.wasm");
    const bits = await workspace.fs.readFile(filename);
    const module = await WebAssembly.compile(bits);
    const wasmProcess = await wasm.createProcess(
      "cov",
      module,
      { initial: 32768, maximum: 32768, shared: true },
      options,
    );

    const decoder = new TextDecoder("utf-8");
    wasmProcess.stderr!.onData((data) => {
      channel.append(decoder.decode(data));
    });

    return startServer(wasmProcess);
  };

  const clientOptions: LanguageClientOptions = {
    documentSelector,
    outputChannel: channel,
    uriConverters,
  };

  return {
    client: new LanguageClient(
      "covalence-lsp",
      "Covalence LSP",
      serverOptions,
      clientOptions,
    ),
    toServerPath: (uri) => fileUriToPath(uriConverters.code2Protocol(uri)),
    mode: "wasm",
    description: "wasm",
  };
}
