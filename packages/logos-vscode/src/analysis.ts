// Pure, editor-independent analysis for the Logos language server.
// Kept free of any LSP connection so it can be unit-tested in plain Node.
import {
  Diagnostic,
  DiagnosticSeverity,
  InlayHint,
  InlayHintKind,
  Position,
  Range,
} from "vscode-languageserver";

export const TOKEN_TYPES = [
  "keyword",
  "type",
  "function",
  "variable",
  "comment",
  "string",
  "number",
] as const;
export type TokenTypeName = (typeof TOKEN_TYPES)[number];

export const TOKEN_MODIFIERS = ["declaration", "defaultLibrary"] as const;
export type TokenModifierName = (typeof TOKEN_MODIFIERS)[number];

export type SemanticToken = {
  line: number;
  start: number;
  length: number;
  tokenType: TokenTypeName;
  modifiers: TokenModifierName[];
};

const DIAGNOSTIC_SOURCE = "LOGOS Language Server";

// Reserved words from the grammar (logos_lang/grammar.py) and FORMAL_LANGUAGE_SPEC.md §2.5.
const KEYWORD_LIST = [
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
  "as",
  "transfigure",
  "into",
  "supplicate",
  "write",
  "mystery",
  "icon",
  "is",
  "not",
  "Verily",
  "Nay",
];
export const KEYWORDS = new Set(KEYWORD_LIST);

const TYPE_LIST = [
  "HolyInt",
  "Int",
  "HolyFloat",
  "Float",
  "Double",
  "Text",
  "String",
  "Bool",
  "Procession",
  "Mystery",
  "Void",
  "None",
];

export const BUILTIN_FUNCTIONS = new Set([
  "measure",
  "append",
  "adorn",
  "extract",
  "purge",
  "passage",
  "now",
  "env",
  "argv",
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
const REGEX_KEYWORDS = new RegExp(`\\b(?:${KEYWORD_LIST.join("|")})\\b`, "g");
const REGEX_TYPES = new RegExp(`\\b(?:${TYPE_LIST.join("|")})\\b`, "g");
const REGEX_FUNCTION_DECL = /\bmystery\s+([a-z][a-z0-9_]*)/g;
const REGEX_ICON_DECL = /\bicon\s+([A-Z][A-Za-z0-9_]*)/g;
const REGEX_VARIABLE_DECL = /\binscribe\s+([A-Za-z_]\w*)/g;
const REGEX_CALL = /\b([A-Za-z_][A-Za-z0-9_]*)\s*(?=\()/g;
// `d` flag: match.indices gives exact capture offsets (no indexOf guessing).
const REGEX_TYPED_INSCRIBE = /\binscribe\s+([A-Za-z_]\w*)\s*:\s*([A-Za-z_]\w*)\s*=\s*(.+?);/d;
const REGEX_AMEND = /\bamend\s+([A-Za-z_]\w*)\s*=\s*(.+?);/d;
const REGEX_STRING_ARITH = /"(?:[^"\\]|\\.)*"\s*[-*\/]\s*\d+/;
const REGEX_INSCRIBE =
  /\binscribe\s+([A-Za-z_]\w*)\s*(?::\s*([A-Za-z_]\w*))?\s*=\s*(.+?)\s*;?\s*$/d;

/** Index where a `//` or `#` line comment starts outside string literals, or -1. */
export function findLineCommentStart(line: string): number {
  let inString = false;
  let escaped = false;

  for (let i = 0; i < line.length; i += 1) {
    const ch = line[i];

    if (inString) {
      if (escaped) {
        escaped = false;
      } else if (ch === "\\") {
        escaped = true;
      } else if (ch === '"') {
        inString = false;
      }
      continue;
    }

    if (ch === '"') {
      inString = true;
    } else if (ch === "#") {
      return i;
    } else if (ch === "/" && line[i + 1] === "/") {
      return i;
    }
  }

  return -1;
}

function stripComment(line: string): string {
  const start = findLineCommentStart(line);
  return start >= 0 ? line.slice(0, start) : line;
}

function splitLines(text: string): string[] {
  return text.split(/\r?\n/);
}

/** The document with comments blanked to spaces, so every offset still maps 1:1. */
function blankComments(text: string): string {
  return splitLines(text)
    .map((line) => {
      const start = findLineCommentStart(line);
      return start >= 0 ? line.slice(0, start) + " ".repeat(line.length - start) : line;
    })
    .join("\n");
}

function lineStartsOf(code: string): number[] {
  const starts = [0];
  for (let i = 0; i < code.length; i += 1) {
    if (code[i] === "\n") starts.push(i + 1);
  }
  return starts;
}

function positionAt(lineStarts: number[], offset: number): Position {
  let lo = 0;
  let hi = lineStarts.length - 1;
  while (lo < hi) {
    const mid = (lo + hi + 1) >> 1;
    if ((lineStarts[mid] ?? 0) <= offset) lo = mid;
    else hi = mid - 1;
  }
  return { line: lo, character: offset - (lineStarts[lo] ?? 0) };
}

/**
 * Keeps only top-level syntax: string contents and anything nested inside (), [] or {}
 * become spaces (offsets are preserved). `foo(a < b)` -> `foo(     )`.
 */
export function topLevel(expr: string): string {
  let out = "";
  let depth = 0;
  let inString = false;
  let escaped = false;
  for (const ch of expr) {
    if (inString) {
      if (escaped) escaped = false;
      else if (ch === "\\") escaped = true;
      else if (ch === '"') inString = false;
      out += !inString && depth === 0 ? '"' : " ";
      continue;
    }
    if (ch === '"') {
      inString = true;
      out += depth === 0 ? '"' : " ";
    } else if ("([{".includes(ch)) {
      out += depth === 0 ? ch : " ";
      depth += 1;
    } else if (")]}".includes(ch)) {
      depth = Math.max(0, depth - 1);
      out += depth === 0 ? ch : " ";
    } else {
      out += depth === 0 ? ch : " ";
    }
  }
  return out;
}

/** True when `expr` is one bracketed group: `[1, [2]]` yes, `[1][0]` / `[1] + [2]` no. */
function isSingleGroup(expr: string, open: string, close: string): boolean {
  if (!expr.startsWith(open) || !expr.endsWith(close)) return false;
  // At top level only the outer opening bracket and the final closing bracket survive.
  return topLevel(expr).replace(/\s/g, "") === `${open}${close}`;
}

export function areTypesCompatible(declared: string, actual: string): boolean {
  const numericFloat = ["HolyFloat", "Float", "Double"];
  const numericInt = ["HolyInt", "Int"];
  const text = ["Text", "String"];
  const bool = ["Bool", "Verily", "Nay"];
  if (declared === actual || declared === "Mystery") return true;
  if (numericFloat.includes(declared) && [...numericInt, ...numericFloat].includes(actual)) {
    return true;
  }
  if (numericInt.includes(declared) && numericInt.includes(actual)) return true;
  if (text.includes(declared) && text.includes(actual)) return true;
  if (bool.includes(declared) && bool.includes(actual)) return true;
  return false;
}

function typeError(range: Range, message: string): Diagnostic {
  return {
    severity: DiagnosticSeverity.Error,
    range,
    message: `Heresy: Type mismatch: ${message}`,
    source: DIAGNOSTIC_SOURCE,
  };
}

function escapeRegExp(text: string): string {
  return text.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
}

// --- Lexical scopes -------------------------------------------------------------------
// Each `{ ... }` opens a scope, identified by its chain of ancestor ids ("0/3/7").
// A declaration is visible wherever its chain is a prefix of the use site's chain.

function scopeChains(code: string): string[] {
  const chains = new Array<string>(code.length);
  const stack = [0];
  let nextId = 1;
  let chain = "0";
  let inString = false;
  let escaped = false;
  for (let i = 0; i < code.length; i += 1) {
    const ch = code[i];
    if (inString) {
      if (escaped) escaped = false;
      else if (ch === "\\") escaped = true;
      else if (ch === '"' || ch === "\n") inString = false;
    } else if (ch === '"') {
      inString = true;
    } else if (ch === "{") {
      stack.push(nextId);
      nextId += 1;
      chain = stack.join("/");
    } else if (ch === "}") {
      chains[i] = chain; // the closing brace still belongs to the inner scope
      if (stack.length > 1) stack.pop();
      chain = stack.join("/");
      continue;
    }
    chains[i] = chain;
  }
  return chains;
}

type Declaration = { name: string; type: string; scope: string; offset: number };

const REGEX_TYPED_DECL = /\binscribe\s+([A-Za-z_]\w*)\s*:\s*([A-Za-z_]\w*)/;
const REGEX_MYSTERY_HEAD =
  /\bmystery\s+[a-z][a-z0-9_]*\s*\(([^)]*)\)\s*(?:->\s*[A-Za-z_]\w*\s*)?\{/;
const REGEX_TYPED_PARAM = /([A-Za-z_]\w*)\s*:\s*([A-Za-z_]\w*)/;

function collectDeclarations(code: string, scopes: string[]): Declaration[] {
  const declarations: Declaration[] = [];
  forEachMatch(REGEX_TYPED_DECL, code, (m) => {
    declarations.push({
      name: m[1] ?? "",
      type: m[2] ?? "",
      scope: scopes[m.index] ?? "0",
      offset: m.index,
    });
  });
  // Typed parameters belong to the function body's scope (the `{` the head ends with).
  forEachMatch(REGEX_MYSTERY_HEAD, code, (m) => {
    const bodyScope = scopes[m.index + m[0].length - 1] ?? "0";
    const paramsStart = m.indices?.[1]?.[0] ?? m.index;
    forEachMatch(REGEX_TYPED_PARAM, m[1] ?? "", (p) => {
      declarations.push({
        name: p[1] ?? "",
        type: p[2] ?? "",
        scope: bodyScope,
        offset: paramsStart + p.index,
      });
    });
  });
  return declarations;
}

function lookupDeclaredType(
  declarations: Declaration[],
  name: string,
  useOffset: number,
  scopes: string[]
): string | null {
  const useScope = scopes[useOffset] ?? "0";
  let best: Declaration | undefined;
  let bestDepth = -1;
  let bestOrder = -Infinity;
  for (const decl of declarations) {
    const visible = useScope === decl.scope || useScope.startsWith(`${decl.scope}/`);
    if (decl.name !== name || !visible) continue;
    // Innermost scope wins; within it, the latest declaration before the use site.
    const depth = decl.scope.split("/").length;
    const order = decl.offset <= useOffset ? decl.offset : -decl.offset;
    if (depth > bestDepth || (depth === bestDepth && order > bestOrder)) {
      best = decl;
      bestDepth = depth;
      bestOrder = order;
    }
  }
  return best?.type ?? null;
}

export function inferType(expression: string): string | null {
  let expr = expression.trim();
  // `(a < b)` has the type of `a < b`.
  while (isSingleGroup(expr, "(", ")")) {
    expr = expr.slice(1, -1).trim();
  }
  if (!expr) {
    return null;
  }

  if (/^(Verily|Nay)$/.test(expr)) {
    return "Bool";
  }
  if (/^"(?:[^"\\]|\\.)*"$/.test(expr)) {
    return "Text";
  }
  if (/^-?\d+\.\d+$/.test(expr)) {
    return "HolyFloat";
  }
  if (/^-?\d+$/.test(expr)) {
    return "HolyInt";
  }
  if (isSingleGroup(expr, "[", "]")) {
    return "Procession";
  }

  const writeIconMatch = /^write\s+([A-Z][A-Za-z0-9_]*)\s*\{/.exec(expr);
  if (writeIconMatch && isSingleGroup(expr.slice(expr.indexOf("{")), "{", "}")) {
    return writeIconMatch[1] ?? null;
  }

  const outer = topLevel(expr);
  if (/^transfigure\b/.test(outer)) {
    const castMatch = /\binto\s+([A-Za-z_][A-Za-z0-9_]*)\s*$/.exec(outer);
    if (castMatch) {
      return castMatch[1] ?? null;
    }
  }

  // Only a comparison at the top level makes the whole expression Bool.
  if (/\bis\b|<=|>=|<|>/.test(outer)) {
    return "Bool";
  }

  return null;
}

export function computeDiagnostics(text: string): Diagnostic[] {
  const diagnostics: Diagnostic[] = [];
  const code = blankComments(text);
  const lineStarts = lineStartsOf(code);
  const scopes = scopeChains(code);
  const declarations = collectDeclarations(code, scopes);
  const rangeOf = (start: number, end: number): Range => ({
    start: positionAt(lineStarts, start),
    end: positionAt(lineStarts, end),
  });
  const groupRange = (m: RegExpExecArray, group: number): Range => {
    const span = m.indices?.[group] ?? [m.index, m.index + m[0].length];
    return rangeOf(span[0], span[1]);
  };

  // Global matching: every statement on a line is checked, not just the first.
  forEachMatch(REGEX_TYPED_INSCRIBE, code, (m) => {
    const declaredType = m[2] ?? "";
    const inferred = inferType(m[3] ?? "");
    if (inferred && !areTypesCompatible(declaredType, inferred)) {
      diagnostics.push(
        typeError(groupRange(m, 2), `declared ${declaredType} but assigned ${inferred}.`)
      );
    }
  });

  forEachMatch(REGEX_AMEND, code, (m) => {
    const varName = m[1] ?? "";
    const inferred = inferType(m[2] ?? "");
    const declaredType = lookupDeclaredType(declarations, varName, m.index, scopes);
    if (declaredType && inferred && !areTypesCompatible(declaredType, inferred)) {
      diagnostics.push(
        typeError(groupRange(m, 1), `'${varName}' is ${declaredType} but amended with ${inferred}.`)
      );
    }
  });

  forEachMatch(REGEX_STRING_ARITH, code, (m) => {
    diagnostics.push(
      typeError(
        rangeOf(m.index, m.index + m[0].length),
        "invalid operator between Text and HolyInt."
      )
    );
  });

  diagnostics.sort(
    (a, b) =>
      a.range.start.line - b.range.start.line ||
      a.range.start.character - b.range.start.character
  );
  return diagnostics;
}

export function computeSemanticTokens(text: string): SemanticToken[] {
  const tokens: SemanticToken[] = [];
  const iconNames = new Set<string>();
  forEachMatch(REGEX_ICON_DECL, blankComments(text), (m) => {
    if (m[1]) iconNames.add(m[1]);
  });
  const userTypes = iconNames.size
    ? new RegExp(`\\b(?:${[...iconNames].map(escapeRegExp).join("|")})\\b`)
    : null;

  splitLines(text).forEach((lineText, line) => {
    const mask = new Array<boolean>(lineText.length).fill(false);
    const lineTokens: SemanticToken[] = [];
    const queue = (
      start: number,
      length: number,
      tokenType: TokenTypeName,
      modifiers: TokenModifierName[] = []
    ): void => {
      if (length <= 0 || start < 0 || start >= mask.length) return;
      const safeLength = Math.min(length, mask.length - start);
      for (let i = start; i < start + safeLength; i += 1) {
        if (mask[i]) return;
      }
      mask.fill(true, start, start + safeLength);
      lineTokens.push({ line, start, length: safeLength, tokenType, modifiers });
    };

    const commentStart = findLineCommentStart(lineText);
    if (commentStart >= 0) {
      queue(commentStart, lineText.length - commentStart, "comment");
    }
    const code = commentStart >= 0 ? lineText.slice(0, commentStart) : lineText;

    const addMatches = (
      pattern: RegExp,
      tokenType: TokenTypeName,
      modifiers: TokenModifierName[] = [],
      group = 0
    ): void => {
      forEachMatch(pattern, code, (match) => {
        const span = match.indices?.[group];
        if (span) queue(span[0], span[1] - span[0], tokenType, modifiers);
      });
    };

    addMatches(REGEX_STRING, "string");
    addMatches(REGEX_NUMBER, "number");
    addMatches(REGEX_KEYWORDS, "keyword");
    addMatches(REGEX_TYPES, "type");
    addMatches(REGEX_FUNCTION_DECL, "function", ["declaration"], 1);
    addMatches(REGEX_ICON_DECL, "type", ["declaration"], 1);
    if (userTypes) addMatches(userTypes, "type");
    addMatches(REGEX_VARIABLE_DECL, "variable", ["declaration"], 1);

    forEachMatch(REGEX_CALL, code, (match) => {
      const fnName = match[1];
      const span = match.indices?.[1];
      if (!fnName || !span || KEYWORDS.has(fnName)) return;
      queue(
        span[0],
        fnName.length,
        "function",
        BUILTIN_FUNCTIONS.has(fnName) ? ["defaultLibrary"] : []
      );
    });

    lineTokens.sort((a, b) => a.start - b.start);
    tokens.push(...lineTokens);
  });

  return tokens;
}

export function computeInlayHints(text: string, startLine: number, endLine: number): InlayHint[] {
  const hints: InlayHint[] = [];
  const lines = splitLines(text);
  const upperBound = Math.min(lines.length - 1, endLine);

  for (let line = Math.max(0, startLine); line <= upperBound; line += 1) {
    const code = stripComment(lines[line] ?? "");
    const match = REGEX_INSCRIBE.exec(code);
    if (!match || match[2]) {
      continue; // no declaration, or already explicitly typed
    }
    const inferred = inferType(match[3] ?? "");
    const nameSpan = match.indices?.[1];
    if (!inferred || !nameSpan) {
      continue;
    }
    hints.push({
      position: { line, character: nameSpan[1] },
      kind: InlayHintKind.Type,
      label: `: ${inferred}`,
      paddingLeft: true,
    });
  }

  return hints;
}

function forEachMatch(
  pattern: RegExp,
  text: string,
  visitor: (match: RegExpExecArray) => void
): void {
  const flags = new Set(pattern.flags);
  flags.add("g");
  flags.add("d");
  const regex = new RegExp(pattern.source, [...flags].join(""));
  let match: RegExpExecArray | null;
  while ((match = regex.exec(text)) !== null) {
    visitor(match);
    if (match[0].length === 0) {
      regex.lastIndex += 1;
    }
  }
}
