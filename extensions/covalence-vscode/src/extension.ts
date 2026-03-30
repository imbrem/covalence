import { ExtensionContext, Uri, commands, window, workspace } from "vscode";
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

let client: LanguageClient | undefined;

export async function activate(context: ExtensionContext) {
  const channel = window.createOutputChannel("Covalence LSP");
  const wasm: Wasm = await Wasm.load();

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

  const clientOptions: LanguageClientOptions = {
    documentSelector: [{ language: "ion" }],
    outputChannel: channel,
    uriConverters: createUriConverters(),
  };

  client = new LanguageClient(
    "covalence-lsp",
    "Covalence LSP",
    serverOptions,
    clientOptions,
  );

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

  await client.start();
  channel.appendLine("Covalence LSP started.");
}

export async function deactivate() {
  if (client) {
    await client.stop();
    client = undefined;
  }
}
