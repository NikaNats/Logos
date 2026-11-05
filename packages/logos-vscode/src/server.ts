import {
  createConnection,
  InitializeParams,
  InitializeResult,
  ProposedFeatures,
  SemanticTokensBuilder,
  SemanticTokensLegend,
  TextDocuments,
  TextDocumentSyncKind,
} from "vscode-languageserver/node";
import { TextDocument } from "vscode-languageserver-textdocument";

import {
  computeDiagnostics,
  computeInlayHints,
  computeSemanticTokens,
  TOKEN_MODIFIERS,
  TOKEN_TYPES,
  TokenModifierName,
} from "./analysis";

const connection = createConnection(ProposedFeatures.all);
const documents: TextDocuments<TextDocument> = new TextDocuments(TextDocument);

const SEMANTIC_LEGEND: SemanticTokensLegend = {
  tokenTypes: [...TOKEN_TYPES],
  tokenModifiers: [...TOKEN_MODIFIERS],
};

function modifierBitset(modifiers: TokenModifierName[]): number {
  return modifiers.reduce((acc, modifier) => acc | (1 << TOKEN_MODIFIERS.indexOf(modifier)), 0);
}

connection.onInitialize((_params: InitializeParams): InitializeResult => ({
  capabilities: {
    textDocumentSync: TextDocumentSyncKind.Incremental,
    semanticTokensProvider: {
      legend: SEMANTIC_LEGEND,
      full: true,
    },
    inlayHintProvider: true,
  },
}));

connection.languages.semanticTokens.on((params) => {
  const document = documents.get(params.textDocument.uri);
  if (!document) {
    return { data: [] };
  }
  const builder = new SemanticTokensBuilder();
  for (const token of computeSemanticTokens(document.getText())) {
    builder.push(
      token.line,
      token.start,
      token.length,
      TOKEN_TYPES.indexOf(token.tokenType),
      modifierBitset(token.modifiers)
    );
  }
  return builder.build();
});

connection.languages.inlayHint.on((params) => {
  const document = documents.get(params.textDocument.uri);
  if (!document) {
    return [];
  }
  return computeInlayHints(document.getText(), params.range.start.line, params.range.end.line);
});

documents.onDidChangeContent((change) => {
  connection.sendDiagnostics({
    uri: change.document.uri,
    diagnostics: computeDiagnostics(change.document.getText()),
  });
});

documents.listen(connection);
connection.listen();
