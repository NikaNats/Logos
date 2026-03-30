import {
  createConnection,
  InlayHint,
  InlayHintKind,
  InitializeParams,
  InitializeResult,
  ProposedFeatures,
  SemanticTokensBuilder,
  SemanticTokensLegend,
  TextDocuments,
  TextDocumentSyncKind,
} from "vscode-languageserver/node";
import { TextDocument } from "vscode-languageserver-textdocument";

const connection = createConnection(ProposedFeatures.all);
const documents: TextDocuments<TextDocument> = new TextDocuments(TextDocument);

const TOKEN_TYPES = [
  "keyword",
  "type",
  "function",
  "variable",
  "comment",
  "string",
  "number",
] as const;

type TokenTypeName = (typeof TOKEN_TYPES)[number];

const TOKEN_MODIFIERS = ["declaration", "defaultLibrary"] as const;
type TokenModifierName = (typeof TOKEN_MODIFIERS)[number];

type QueuedToken = {
  line: number;
  start: number;
  length: number;
  tokenType: TokenTypeName;
  modifiers: TokenModifierName[];
};

const TOKEN_TYPE_INDEX: Record<TokenTypeName, number> = {
  keyword: 0,
  type: 1,
  function: 2,
  variable: 3,
  comment: 4,
  string: 5,
  number: 6,
};

const TOKEN_MODIFIER_INDEX: Record<TokenModifierName, number> = {
  declaration: 0,
  defaultLibrary: 1,
};

const SEMANTIC_LEGEND: SemanticTokensLegend = {
  tokenTypes: [...TOKEN_TYPES],
  tokenModifiers: [...TOKEN_MODIFIERS],
};

const KEYWORDS = new Set([
  "chant",
  "discern",
  "otherwise",
  "vigil",
  "confess",
  "amen",
  "contemplate",
  "aspect",
  "silence",
  "proclaim",
  "inscribe",
  "amend",
  "offer",
  "apocrypha",
  "tradition",
  "transfigure",
  "into",
  "supplicate",
  "write",
  "mystery",
  "icon",
  "Verily",
  "Nay",
]);

const BUILTIN_FUNCTIONS = new Set([
  "measure",
  "append",
  "extract",
  "purge",
  "passage",
  "now",
  "env",
  "__sys_time",
  "__sys_env",
  "__sys_sleep",
  "__sys_exit",
  "__sys_open",
  "__sys_close",
  "__sys_write",
  "__sys_read",
  "__sys_str",
]);

const REGEX_STRING = /"(?:[^"\\]|\\.)*"/g;
const REGEX_NUMBER = /\b\d+(?:\.\d+)?\b/g;
const REGEX_KEYWORDS =
  /\b(?:chant|discern|otherwise|vigil|confess|amen|contemplate|aspect|silence|proclaim|inscribe|amend|offer|apocrypha|tradition|transfigure|into|supplicate|write|mystery|icon|Verily|Nay)\b/g;
const REGEX_TYPES =
  /\b(?:HolyInt|Int|HolyFloat|Float|Double|Text|String|Bool|Procession|Void|None)\b/g;
const REGEX_FUNCTION_DECL = /\bmystery\s+([a-z][a-z0-9_]*)/g;
const REGEX_ICON_DECL = /\bicon\s+([A-Z][A-Za-z0-9_]*)/g;
const REGEX_VARIABLE_DECL = /\binscribe\s+([A-Za-z_]\w*)/g;
const REGEX_CALL = /\b([A-Za-z_][A-Za-z0-9_]*)\s*(?=\()/g;
const REGEX_INSCRIBE =
  /\binscribe\s+([A-Za-z_]\w*)\s*(?::\s*([A-Za-z_]\w*))?\s*=\s*(.+?)\s*;?\s*$/;

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
  return computeSemanticTokens(document);
});

connection.languages.inlayHint.on((params) => {
  const document = documents.get(params.textDocument.uri);
  if (!document) {
    return [];
  }
  return computeInlayHints(document, params.range.start.line, params.range.end.line);
});

function computeSemanticTokens(document: TextDocument) {
  const builder = new SemanticTokensBuilder();
  const lines = document.getText().split(/\r?\n/);

  lines.forEach((lineText, lineNumber) => {
    const mask = new Array<boolean>(lineText.length).fill(false);
    const queuedTokens: QueuedToken[] = [];
    const commentStart = findLineCommentStart(lineText);

    if (commentStart >= 0) {
      queueToken(
        queuedTokens,
        mask,
        lineNumber,
        commentStart,
        lineText.length - commentStart,
        "comment"
      );
    }

    const codePart = commentStart >= 0 ? lineText.slice(0, commentStart) : lineText;

    addRegexMatches(queuedTokens, mask, lineNumber, codePart, REGEX_STRING, "string");
    addRegexMatches(queuedTokens, mask, lineNumber, codePart, REGEX_NUMBER, "number");
    addRegexMatches(queuedTokens, mask, lineNumber, codePart, REGEX_KEYWORDS, "keyword");
    addRegexMatches(queuedTokens, mask, lineNumber, codePart, REGEX_TYPES, "type");

    addRegexMatches(
      queuedTokens,
      mask,
      lineNumber,
      codePart,
      REGEX_FUNCTION_DECL,
      "function",
      ["declaration"],
      1
    );

    addRegexMatches(
      queuedTokens,
      mask,
      lineNumber,
      codePart,
      REGEX_ICON_DECL,
      "type",
      ["declaration"],
      1
    );

    addRegexMatches(
      queuedTokens,
      mask,
      lineNumber,
      codePart,
      REGEX_VARIABLE_DECL,
      "variable",
      ["declaration"],
      1
    );

    forEachMatch(REGEX_CALL, codePart, (match) => {
      const fnName = match[1];
      if (!fnName || KEYWORDS.has(fnName)) {
        return;
      }
      const start = groupStart(match, 1);
      const modifiers: TokenModifierName[] = BUILTIN_FUNCTIONS.has(fnName)
        ? ["defaultLibrary"]
        : [];
      queueToken(queuedTokens, mask, lineNumber, start, fnName.length, "function", modifiers);
    });

    queuedTokens.sort((a, b) => a.start - b.start);
    queuedTokens.forEach((token) => {
      builder.push(
        token.line,
        token.start,
        token.length,
        TOKEN_TYPE_INDEX[token.tokenType],
        modifierBitset(token.modifiers)
      );
    });
  });

  return builder.build();
}

function computeInlayHints(document: TextDocument, startLine: number, endLine: number): InlayHint[] {
  const hints: InlayHint[] = [];
  const lines = document.getText().split(/\r?\n/);
  const lowerBound = Math.max(0, startLine);
  const upperBound = Math.min(lines.length - 1, endLine);

  for (let lineNumber = lowerBound; lineNumber <= upperBound; lineNumber += 1) {
    const fullLine = lines[lineNumber] ?? "";
    const commentStart = findLineCommentStart(fullLine);
    const codePart = commentStart >= 0 ? fullLine.slice(0, commentStart) : fullLine;

    const match = REGEX_INSCRIBE.exec(codePart);
    REGEX_INSCRIBE.lastIndex = 0;
    if (!match) {
      continue;
    }

    const variableName = match[1];
    const declaredType = match[2];
    const expression = match[3] ?? "";
    if (!variableName || declaredType) {
      continue;
    }

    const inferred = inferType(expression);
    if (!inferred) {
      continue;
    }

    const nameStart = codePart.indexOf(variableName, match.index);
    if (nameStart < 0) {
      continue;
    }

    hints.push({
      position: {
        line: lineNumber,
        character: nameStart + variableName.length,
      },
      kind: InlayHintKind.Type,
      label: `: ${inferred}`,
      paddingLeft: true,
    });
  }

  return hints;
}

function inferType(expression: string): string | null {
  const expr = expression.trim();
  if (!expr) {
    return null;
  }

  if (/^(Verily|Nay)\b/.test(expr)) {
    return "Bool";
  }
  if (/^"(?:[^"\\]|\\.)*"$/.test(expr)) {
    return "Text";
  }
  if (/^-?\d+\.\d+\b/.test(expr)) {
    return "HolyFloat";
  }
  if (/^-?\d+\b/.test(expr)) {
    return "HolyInt";
  }
  if (/^\[/.test(expr)) {
    return "Procession";
  }

  const writeIconMatch = /^write\s+([A-Z][A-Za-z0-9_]*)\s*\{/.exec(expr);
  if (writeIconMatch) {
    return writeIconMatch[1] ?? null;
  }

  if (/^transfigure\b/.test(expr)) {
    const castMatch = /\binto\s+([A-Za-z_][A-Za-z0-9_]*)\s*$/.exec(expr);
    if (castMatch) {
      return castMatch[1] ?? null;
    }
  }

  if (/\bis\s+not\b|\bis\b|<=|>=|==|!=|<|>/.test(expr)) {
    return "Bool";
  }

  return null;
}

function addRegexMatches(
  queuedTokens: QueuedToken[],
  mask: boolean[],
  line: number,
  lineText: string,
  pattern: RegExp,
  tokenType: TokenTypeName,
  modifiers: TokenModifierName[] = [],
  captureGroup = 0
): void {
  forEachMatch(pattern, lineText, (match) => {
    const text = captureGroup === 0 ? match[0] : (match[captureGroup] ?? "");
    if (!text) {
      return;
    }
    const start = captureGroup === 0 ? match.index : groupStart(match, captureGroup);
    queueToken(queuedTokens, mask, line, start, text.length, tokenType, modifiers);
  });
}

function forEachMatch(pattern: RegExp, text: string, visitor: (m: RegExpExecArray) => void): void {
  const flags = pattern.flags.includes("g") ? pattern.flags : `${pattern.flags}g`;
  const regex = new RegExp(pattern.source, flags);
  let match: RegExpExecArray | null;

  while ((match = regex.exec(text)) !== null) {
    visitor(match);
    if (match[0].length === 0) {
      regex.lastIndex += 1;
    }
  }
}

function groupStart(match: RegExpExecArray, group: number): number {
  const groupValue = match[group];
  if (!groupValue) {
    return match.index;
  }
  const localStart = match[0].indexOf(groupValue);
  return localStart >= 0 ? match.index + localStart : match.index;
}

function queueToken(
  queuedTokens: QueuedToken[],
  mask: boolean[],
  line: number,
  start: number,
  length: number,
  tokenType: TokenTypeName,
  modifiers: TokenModifierName[] = []
): void {
  if (length <= 0 || start < 0 || start >= mask.length) {
    return;
  }

  const safeLength = Math.min(length, mask.length - start);
  if (!occupy(mask, start, safeLength)) {
    return;
  }

  queuedTokens.push({
    line,
    start,
    length: safeLength,
    tokenType,
    modifiers,
  });
}

function occupy(mask: boolean[], start: number, length: number): boolean {
  for (let i = start; i < start + length; i += 1) {
    if (mask[i]) {
      return false;
    }
  }
  for (let i = start; i < start + length; i += 1) {
    mask[i] = true;
  }
  return true;
}

function modifierBitset(modifiers: TokenModifierName[]): number {
  return modifiers.reduce((acc, modifier) => acc | (1 << TOKEN_MODIFIER_INDEX[modifier]), 0);
}

function findLineCommentStart(line: string): number {
  let inString = false;
  let escaped = false;

  for (let i = 0; i < line.length - 1; i += 1) {
    const ch = line[i];
    const next = line[i + 1];

    if (inString) {
      if (escaped) {
        escaped = false;
        continue;
      }
      if (ch === "\\") {
        escaped = true;
        continue;
      }
      if (ch === '"') {
        inString = false;
      }
      continue;
    }

    if (ch === '"') {
      inString = true;
      continue;
    }

    if (ch === "/" && next === "/") {
      return i;
    }
  }

  return -1;
}

documents.listen(connection);
connection.listen();
