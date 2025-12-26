import * as path from 'path';
import { ExtensionContext, workspace } from 'vscode';
import {
  LanguageClient,
  LanguageClientOptions,
  ServerOptions,
} from 'vscode-languageclient/node';

let client: LanguageClient | undefined;

export function activate(context: ExtensionContext) {
  const serverPath = context.asAbsolutePath(path.join('server', 'lsp_server.py'));

  const workspaceRoot = workspace.workspaceFolders?.[0]?.uri.fsPath;
  const venvPython = workspaceRoot
    ? (process.platform === 'win32'
        ? path.join(workspaceRoot, '.venv', 'Scripts', 'python.exe')
        : path.join(workspaceRoot, '.venv', 'bin', 'python'))
    : undefined;

  const pythonCommand = venvPython && require('fs').existsSync(venvPython) ? venvPython : 'python';

  const serverOptions: ServerOptions = {
    command: pythonCommand,
    args: [serverPath],
  };

  const clientOptions: LanguageClientOptions = {
    documentSelector: [{ scheme: 'file', language: 'logos' }],
    synchronize: {
      fileEvents: workspace.createFileSystemWatcher('**/.clientrc'),
    },
  };

  client = new LanguageClient(
    'logosLanguageServer',
    'LOGOS Language Server',
    serverOptions,
    clientOptions
  );

  client.start();
}

export function deactivate(): Thenable<void> | undefined {
  if (!client) {
    return undefined;
  }
  return client.stop();
}
