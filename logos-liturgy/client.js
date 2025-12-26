const vscode = require('vscode');
const path = require('path');
const { LanguageClient } = require('vscode-languageclient/node');

let client;

function activate(context) {
  const workspaceFolder = vscode.workspace.workspaceFolders?.[0]?.uri.fsPath;
  if (!workspaceFolder) {
    return;
  }

  const serverPath = path.join(workspaceFolder, 'logos', 'confessor.py');

  const serverOptions = {
    command: 'python',
    args: [serverPath],
    options: {
      cwd: path.join(workspaceFolder, 'logos')
    }
  };

  const clientOptions = {
    documentSelector: [{ scheme: 'file', language: 'logos' }]
  };

  client = new LanguageClient(
    'logosLsp',
    'Logos Confessional',
    serverOptions,
    clientOptions
  );

  context.subscriptions.push(client.start());
}

function deactivate() {
  if (!client) {
    return undefined;
  }
  return client.stop();
}

module.exports = { activate, deactivate };
