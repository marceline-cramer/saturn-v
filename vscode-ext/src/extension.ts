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
    console.log("creating language server");
    const server = new LanguageServer();
    console.log("language server created");
    const writer = Writable.fromWeb(server.requests);
    const reader = Readable.fromWeb(server.responses);
    console.log("language server bound");
    return { server, writer, reader };
  };
}
