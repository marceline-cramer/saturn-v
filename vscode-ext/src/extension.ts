import { LanguageServer } from "saturn-v-lsp";
import { Readable, Writable } from "stream";
import * as vscode from "vscode";
import { LanguageClient, LanguageClientOptions, ServerOptions } from "vscode-languageclient/node";

export async function activate(context: vscode.ExtensionContext) {
  const server = launchLsp();

  const clientOptions: LanguageClientOptions = {
    documentSelector: [{ scheme: "file", language: "kerolox" }]
  };

  const client = new LanguageClient("kerolox", server, clientOptions, true);
  await client.start();

  const dispose = async () => await client.stop();
  context.subscriptions.push({ dispose });
}

export function launchLsp(): ServerOptions {
  return async () => {
    const server = new LanguageServer();
    const writer = Writable.fromWeb(server.requests);
    const reader = Readable.fromWeb(server.responses);
    return { server, writer, reader };
  };
}
