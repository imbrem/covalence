import {
  Disposable,
  EventEmitter,
  ExtensionContext,
  FileChangeEvent,
  FileStat,
  FileSystemProvider,
  FileType,
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

/** Convert a VSCode URI to the protocol URI string the LSP server sees. */
let toServerUri: (uri: Uri) => string;

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
  toServerUri = (uri: Uri) => uriConverters.code2Protocol(uri);

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

  // --- Store File in Content Store ---
  context.subscriptions.push(
    commands.registerCommand("covalence.storeFile", async () => {
      if (!client) {
        window.showErrorMessage("Covalence LSP is not running.");
        return;
      }
      const editor = window.activeTextEditor;
      if (!editor) {
        window.showErrorMessage("No active editor.");
        return;
      }

      await clientReady;
      const result: { hash?: string; error?: string } =
        await client.sendRequest("covalence/storeFile", { uri: toServerUri(editor.document.uri) });

      if (result.error) {
        window.showErrorMessage(`Store failed: ${result.error}`);
      } else if (result.hash) {
        window.showInformationMessage(`BLAKE3: ${result.hash}`);
      }
    }),
  );

  // --- Lookup Hash in Content Store ---
  context.subscriptions.push(
    commands.registerCommand("covalence.lookupHash", async () => {
      if (!client) {
        window.showErrorMessage("Covalence LSP is not running.");
        return;
      }

      const hash = await window.showInputBox({
        prompt: "Enter BLAKE3 hash (64 hex characters)",
        placeHolder: "e.g. af1349b9f5f9a1a6a0404dea36dcc949...",
        validateInput: (value) => {
          if (!/^[0-9a-fA-F]{64}$/.test(value)) {
            return "Hash must be exactly 64 hexadecimal characters";
          }
          return null;
        },
      });
      if (!hash) return;

      await clientReady;
      const result: { content?: string; error?: string } =
        await client!.sendRequest("covalence/lookupHash", { hash });

      if (result.error) {
        window.showErrorMessage(`Lookup failed: ${result.error}`);
        return;
      }

      const doc = await workspace.openTextDocument({
        content: result.content || "",
      });
      await window.showTextDocument(doc);
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
