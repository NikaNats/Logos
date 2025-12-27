import * as fs from 'fs';
import * as path from 'path';
import { ExtensionContext, workspace, window } from 'vscode';
import {
  LanguageClient,
  LanguageClientOptions,
  ServerOptions,
} from 'vscode-languageclient/node';

let client: LanguageClient | undefined;

export function activate(context: ExtensionContext) {
  const serverOptions = resolveServerOptions(context);

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

function resolveServerOptions(context: ExtensionContext): ServerOptions {
  // Option A (professional): prefer a bundled native executable.
  // This avoids requiring users to have Python and dependencies installed.
  const bundledExe = resolveBundledServerExecutable(context);
  if (bundledExe) {
    return { command: bundledExe, args: [] };
  }

  // Dev / fallback: run the Python server.
  const serverPath = context.asAbsolutePath(path.join('server', 'lsp_server.py'));
  const pythonCommand = resolvePythonCommand();

  window.showWarningMessage(
    'Logos: Using Python language server. If it fails to start, install dependencies: pip install -r packages/logos-vscode/server/requirements.txt, or ship a bundled server binary.'
  );

  return {
    command: pythonCommand,
    args: [serverPath],
  };
}

function resolveBundledServerExecutable(context: ExtensionContext): string | undefined {
  // Layout inside VSIX:
  //   server/bin/win32/logos-lang-server.exe
  // (Other platforms can be added later: server/bin/linux/, server/bin/darwin/)
  const candidates: string[] = [];

  if (process.platform === 'win32') {
    candidates.push(
      context.asAbsolutePath(path.join('server', 'bin', 'win32', 'logos-lang-server.exe'))
    );
  } else if (process.platform === 'linux') {
    candidates.push(context.asAbsolutePath(path.join('server', 'bin', 'linux', 'logos-lang-server')));
  } else if (process.platform === 'darwin') {
    candidates.push(context.asAbsolutePath(path.join('server', 'bin', 'darwin', 'logos-lang-server')));
  }

  for (const candidate of candidates) {
    try {
      if (fs.existsSync(candidate)) {
        return candidate;
      }
    } catch {
      // ignore
    }
  }

  return undefined;
}

function resolvePythonCommand(): string {
  const workspaceRoot = workspace.workspaceFolders?.[0]?.uri.fsPath;
  const venvPython = workspaceRoot
    ? process.platform === 'win32'
      ? path.join(workspaceRoot, '.venv', 'Scripts', 'python.exe')
      : path.join(workspaceRoot, '.venv', 'bin', 'python')
    : undefined;

  if (venvPython && fs.existsSync(venvPython)) {
    return venvPython;
  }

  // Best-effort fallback.
  return 'python';
}

export function deactivate(): Thenable<void> | undefined {
  if (!client) {
    return undefined;
  }
  return client.stop();
}
