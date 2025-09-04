import * as vscode from "vscode";
import { Executable, LanguageClient, LanguageClientOptions, ServerOptions } from "vscode-languageclient/node";

export async function activate(context: vscode.ExtensionContext) {
  const serverCommand: Executable = {
    command: "saturn-v",
    args: ["lsp"],
  };

  const serverOptions: ServerOptions = {
    run: serverCommand,
    debug: serverCommand,
  };

  const clientOptions: LanguageClientOptions = {
    documentSelector: [{ scheme: "file", language: "kerolox" }]
  };

  const client = new LanguageClient("kerolox", serverOptions, clientOptions);
  await client.start();

  const dispose = async () => await client.stop();
  context.subscriptions.push({ dispose });
}
