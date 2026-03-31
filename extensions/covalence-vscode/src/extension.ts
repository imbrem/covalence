import {
  CancellationToken,
  Disposable,
  EventEmitter,
  ExtensionContext,
  FileChangeEvent,
  FileStat,
  FileSystemProvider,
  FileType,
  TextDocumentContentProvider,
  Uri,
  commands,
  languages,
  window,
  workspace,
} from "vscode";
import {
  LanguageClient,
  type LanguageClientOptions,
  type ServerOptions,
} from "vscode-languageclient/node";
import { Wasm, type ProcessOptions } from "@vscode/wasm-wasi/v1";
import {
  createStdioOptions,
  createUriConverters,
  startServer,
} from "@vscode/wasm-wasi-lsp";

const ION_BINARY_SCHEME = "ion-binary";
const IROH_BLOB_SCHEME = "iroh-blob";

// Ion Version Marker for Ion 1.0: 0xE0 0x01 0x00 0xEA
function isBinaryIon(bytes: Uint8Array): boolean {
  return (
    bytes.length >= 4 &&
    bytes[0] === 0xe0 &&
    bytes[1] === 0x01 &&
    bytes[2] === 0x00 &&
    bytes[3] === 0xea
  );
}

/** Extract a filesystem path from a file: URI string (e.g. "file:///foo" → "/foo"). */
function fileUriToPath(uri: string): string {
  return decodeURIComponent(uri.replace(/^file:\/\//, ""));
}

let client: LanguageClient | undefined;
let clientReadyResolve: () => void;
const clientReady = new Promise<void>((resolve) => {
  clientReadyResolve = resolve;
});

/** Convert a VSCode URI to the server-side filesystem path the WASI process sees. */
let toServerPath: (uri: Uri) => string;

class IonBinaryFSProvider implements FileSystemProvider {
  private _emitter = new EventEmitter<FileChangeEvent[]>();
  readonly onDidChangeFile = this._emitter.event;

  watch(): Disposable {
    return new Disposable(() => {});
  }

  async stat(uri: Uri): Promise<FileStat> {
    const realUri = uri.with({ scheme: "file" });
    return workspace.fs.stat(realUri);
  }

  readDirectory(): Thenable<[string, FileType][]> {
    throw new Error("Not supported");
  }

  createDirectory(): void {
    throw new Error("Not supported");
  }

  async readFile(uri: Uri): Promise<Uint8Array> {
    await clientReady;
    const path = toServerPath(uri.with({ scheme: "file" }));

    const result: { text?: string; error?: string } =
      await client!.sendRequest("covalence/decodeBinaryIon", { path });

    if (result.error) {
      throw new Error(`Failed to decode binary Ion: ${result.error}`);
    }

    return new TextEncoder().encode(result.text || "");
  }

  async writeFile(uri: Uri, content: Uint8Array): Promise<void> {
    await clientReady;
    const path = toServerPath(uri.with({ scheme: "file" }));
    const text = new TextDecoder().decode(content);

    const result: { error?: string } = await client!.sendRequest(
      "covalence/encodeBinaryIon",
      { path, text },
    );

    if (result.error) {
      throw new Error(`Failed to encode binary Ion: ${result.error}`);
    }
  }

  delete(): void {
    throw new Error("Not supported");
  }

  rename(): void {
    throw new Error("Not supported");
  }
}

class IrohBlobContentProvider implements TextDocumentContentProvider {
  private _blobCache = new Map<string, string>();

  cacheBlob(hash: string, content: string): void {
    this._blobCache.set(hash, content);
  }

  provideTextDocumentContent(uri: Uri, _token: CancellationToken): string {
    const hash = uri.authority;
    return this._blobCache.get(hash) ?? "";
  }
}

/** Format raw bytes as a hex dump (16 bytes per line with ASCII sidebar). */
function hexDump(bytes: Uint8Array): string {
  const lines: string[] = [];
  for (let offset = 0; offset < bytes.length; offset += 16) {
    const chunk = bytes.slice(offset, offset + 16);
    const hex = Array.from(chunk)
      .map((b) => b.toString(16).padStart(2, "0"))
      .join(" ");
    const ascii = Array.from(chunk)
      .map((b) => (b >= 0x20 && b <= 0x7e ? String.fromCharCode(b) : "."))
      .join("");
    const addr = offset.toString(16).padStart(8, "0");
    lines.push(`${addr}  ${hex.padEnd(47)}  |${ascii}|`);
  }
  return lines.join("\n");
}

async function openAsBinaryIon(fileUri: Uri): Promise<void> {
  const ionUri = fileUri.with({ scheme: ION_BINARY_SCHEME });
  const doc = await workspace.openTextDocument(ionUri);
  await languages.setTextDocumentLanguage(doc, "ion");
  await window.showTextDocument(doc);
}

export async function activate(context: ExtensionContext) {
  const channel = window.createOutputChannel("Covalence LSP");
  const wasm: Wasm = await Wasm.load();

  // Register file system provider for binary Ion viewing/editing
  context.subscriptions.push(
    workspace.registerFileSystemProvider(
      ION_BINARY_SCHEME,
      new IonBinaryFSProvider(),
    ),
  );

  const serverOptions: ServerOptions = async () => {
    const options: ProcessOptions = {
      stdio: createStdioOptions(),
      mountPoints: [{ kind: "workspaceFolder" }],
    };

    const filename = Uri.joinPath(
      context.extensionUri,
      "dist",
      "covalence-lsp.wasm",
    );
    const bits = await workspace.fs.readFile(filename);
    const module = await WebAssembly.compile(bits);
    const process = await wasm.createProcess(
      "covalence-lsp",
      module,
      { initial: 160, maximum: 160, shared: true },
      options,
    );

    const decoder = new TextDecoder("utf-8");
    process.stderr!.onData((data) => {
      channel.append(decoder.decode(data));
    });

    return startServer(process);
  };

  const uriConverters = createUriConverters();
  toServerPath = (uri: Uri) =>
    fileUriToPath(uriConverters.code2Protocol(uri));

  const clientOptions: LanguageClientOptions = {
    documentSelector: [
      { language: "ion" },
      { language: "smt" },
      { language: "alethe" },
    ],
    outputChannel: channel,
    uriConverters,
  };

  client = new LanguageClient(
    "covalence-lsp",
    "Covalence LSP",
    serverOptions,
    clientOptions,
  );

  // --- Serialize Binary Ion command (existing) ---
  context.subscriptions.push(
    commands.registerCommand("covalence.serializeBinaryIon", async () => {
      if (!client) {
        window.showErrorMessage("Covalence LSP is not running.");
        return;
      }
      const editor = window.activeTextEditor;
      if (!editor) {
        window.showErrorMessage("No active editor.");
        return;
      }
      const langId = editor.document.languageId;
      const allowed = ["ion", "json", "jsonc", "json5", "jsonl"];
      if (!allowed.includes(langId)) {
        window.showErrorMessage(
          `Unsupported language: ${langId}. Supported: ${allowed.join(", ")}`,
        );
        return;
      }
      const text = editor.document.getText();
      const result: { byteCount?: number; error?: string } =
        await client.sendRequest("covalence/serializeBinaryIon", { text });
      if (result.error) {
        window.showErrorMessage(`Ion serialization failed: ${result.error}`);
      } else {
        window.showInformationMessage(
          `Binary Ion: ${result.byteCount} bytes`,
        );
      }
    }),
  );

  // --- Convert to Ion 1.0 Binary ---
  context.subscriptions.push(
    commands.registerCommand("covalence.convertToIonBinary", async () => {
      const editor = window.activeTextEditor;
      if (!editor) {
        window.showErrorMessage("No active editor.");
        return;
      }
      if (editor.document.uri.scheme === ION_BINARY_SCHEME) {
        window.showInformationMessage("This file is already binary Ion.");
        return;
      }
      if (
        editor.document.uri.scheme !== "file" ||
        !editor.document.fileName.endsWith(".ion")
      ) {
        window.showErrorMessage(
          "Convert to Binary is only available for text .ion files.",
        );
        return;
      }

      await clientReady;
      const text = editor.document.getText();
      const path = toServerPath(editor.document.uri);

      const result: { error?: string } = await client!.sendRequest(
        "covalence/encodeBinaryIon",
        { path, text },
      );

      if (result.error) {
        window.showErrorMessage(`Failed to encode: ${result.error}`);
        return;
      }

      // Close without saving — we already wrote binary via the LSP, so a
      // normal save would overwrite it with the stale text content.
      await commands.executeCommand(
        "workbench.action.revertAndCloseActiveEditor",
      );
      await openAsBinaryIon(editor.document.uri);

      window.showInformationMessage("Converted to Ion 1.0 Binary.");
    }),
  );

  // --- Convert to Ion 1.0 Text ---
  context.subscriptions.push(
    commands.registerCommand("covalence.convertToIonText", async () => {
      const editor = window.activeTextEditor;
      if (!editor) {
        window.showErrorMessage("No active editor.");
        return;
      }

      const uri = editor.document.uri;
      let fileUri: Uri;

      if (uri.scheme === ION_BINARY_SCHEME) {
        fileUri = uri.with({ scheme: "file" });
      } else if (uri.scheme === "file" && uri.path.endsWith(".ion")) {
        const bytes = await workspace.fs.readFile(uri);
        if (!isBinaryIon(bytes)) {
          window.showInformationMessage("This file is already text Ion.");
          return;
        }
        fileUri = uri;
      } else {
        window.showErrorMessage(
          "Convert to Text is only available for binary .ion files.",
        );
        return;
      }

      if (!fileUri.path.endsWith(".ion")) {
        window.showErrorMessage(
          "Convert to Text is only available for .ion files.",
        );
        return;
      }

      // Capture the decoded text before closing — getText() includes unsaved edits.
      const text = editor.document.getText();

      // Close without saving first to prevent the FSP from re-encoding to
      // binary (which would overwrite the text we're about to write).
      await commands.executeCommand(
        "workbench.action.revertAndCloseActiveEditor",
      );

      // Now write text Ion to the real file
      await workspace.fs.writeFile(fileUri, new TextEncoder().encode(text));
      const doc = await workspace.openTextDocument(fileUri);
      await window.showTextDocument(doc);

      window.showInformationMessage("Converted to Ion 1.0 Text.");
    }),
  );

  // --- View Blob (iroh) ---
  const blobProvider = new IrohBlobContentProvider();
  context.subscriptions.push(
    workspace.registerTextDocumentContentProvider(
      IROH_BLOB_SCHEME,
      blobProvider,
    ),
  );

  // Load the covalence-store WASM module (wasm-bindgen output).
  const storeWasmUri = Uri.joinPath(
    context.extensionUri,
    "dist",
    "covalence_store_bg.wasm",
  );
  const storeJsUri = Uri.joinPath(
    context.extensionUri,
    "dist",
    "covalence_store.js",
  );

  let storeModule: { fetch_blob: (ticket: string) => Promise<Uint8Array> } | undefined;

  async function getStoreModule() {
    if (storeModule) return storeModule;
    // Dynamic import of the wasm-bindgen generated JS glue.
    // The build step copies covalence_store.js and covalence_store_bg.wasm to dist/.
    // We need to use a dynamic import for the JS module, but in the bundled extension
    // we inline it via esbuild. The glue calls `new URL(..., import.meta.url)` to find
    // the .wasm file, but we override the init path manually.
    const glueBytes = await workspace.fs.readFile(storeJsUri);
    const glueText = new TextDecoder().decode(glueBytes);
    // Create a blob URL so we can dynamically import the JS module.
    const blob = new Blob([glueText], { type: "application/javascript" });
    const blobUrl = URL.createObjectURL(blob);
    try {
      const mod = await import(/* webpackIgnore: true */ blobUrl);
      const wasmBytes = await workspace.fs.readFile(storeWasmUri);
      await mod.default(wasmBytes);
      storeModule = mod;
      return mod;
    } finally {
      URL.revokeObjectURL(blobUrl);
    }
  }

  context.subscriptions.push(
    commands.registerCommand("covalence.viewBlob", async () => {
      const ticket = await window.showInputBox({
        prompt: "Enter an iroh blob ticket",
        placeHolder: "blob...",
      });
      if (!ticket) return;

      let store;
      try {
        store = await getStoreModule();
      } catch (e: any) {
        window.showErrorMessage(`Failed to load iroh store module: ${e.message ?? e}`);
        return;
      }

      try {
        await window.withProgress(
          { location: { viewId: "" }, title: "Fetching blob from iroh..." },
          async () => {
            const bytes: Uint8Array = await store!.fetch_blob(ticket);
            // Use the first 16 hex chars of the BLAKE3 hash (from the ticket) as a label.
            const hashLabel = ticket.length > 20 ? ticket.slice(4, 20) : ticket.slice(0, 16);
            const content = hexDump(bytes);
            blobProvider.cacheBlob(hashLabel, content);

            const uri = Uri.parse(`${IROH_BLOB_SCHEME}://${hashLabel}/blob.hex`);
            const doc = await workspace.openTextDocument(uri);
            await window.showTextDocument(doc, { preview: true });
          },
        );
      } catch (e: any) {
        window.showErrorMessage(`Failed to fetch blob: ${e.message ?? e}`);
      }
    }),
  );

  // --- Intercept .10n and binary .ion file opens ---
  const redirecting = new Set<string>();

  context.subscriptions.push(
    window.onDidChangeActiveTextEditor(async (editor) => {
      if (!editor) return;
      const doc = editor.document;
      if (doc.uri.scheme !== "file") return;

      const key = doc.uri.toString();
      if (redirecting.has(key)) return;

      let shouldRedirect = false;

      if (doc.fileName.endsWith(".10n")) {
        shouldRedirect = true;
      } else if (doc.fileName.endsWith(".ion")) {
        try {
          const bytes = await workspace.fs.readFile(doc.uri);
          shouldRedirect = isBinaryIon(bytes);
        } catch {
          // If we can't read the file, don't redirect
        }
      }

      if (!shouldRedirect) return;
      if (window.activeTextEditor !== editor) return;

      redirecting.add(key);
      try {
        await commands.executeCommand("workbench.action.closeActiveEditor");
        await openAsBinaryIon(doc.uri);
      } finally {
        redirecting.delete(key);
      }
    }),
  );

  await client.start();
  clientReadyResolve();
  channel.appendLine("Covalence LSP started.");
}

export async function deactivate() {
  if (client) {
    await client.stop();
    client = undefined;
  }
}
