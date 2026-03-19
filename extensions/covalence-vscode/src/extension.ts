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
    commands.registerCommand("covalence.helloWorld", async () => {
      if (!client) {
        window.showErrorMessage("Covalence LSP is not running.");
        return;
      }
      const result: { message: string } = await client.sendRequest(
        "covalence/helloWorld",
      );
      window.showInformationMessage(result.message);
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
