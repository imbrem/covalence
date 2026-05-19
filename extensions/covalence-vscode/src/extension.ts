import { ExtensionContext, commands, window } from "vscode";
import { type LanguageClient } from "vscode-languageclient/node";
import { createLspServer } from "./server";

let client: LanguageClient | undefined;

export async function activate(context: ExtensionContext) {
  const channel = window.createOutputChannel("Covalence LSP");

  async function startLsp() {
    const server = await createLspServer({
      context,
      channel,
      documentSelector: [
        { language: "smt" },
        { language: "alethe" },
        { language: "cov" },
        { language: "wat" },
      ],
    });

    client = server.client;

    await client.start();

    const serverVersion =
      client.initializeResult?.serverInfo?.version ?? "unknown";
    const startMsg = `Covalence LSP: ${serverVersion} (${server.mode})`;
    channel.appendLine(startMsg);
    window.showInformationMessage(startMsg);
  }

  // --- Restart LSP command ---
  context.subscriptions.push(
    commands.registerCommand("covalence.restartLsp", async () => {
      if (client) {
        await client.stop();
        client = undefined;
      }
      channel.appendLine("Restarting Covalence LSP...");
      await startLsp();
    }),
  );

  await startLsp();
}

export async function deactivate() {
  if (client) {
    await client.stop();
    client = undefined;
  }
}
