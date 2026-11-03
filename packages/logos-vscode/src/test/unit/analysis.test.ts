// Plain-Node unit tests for the primary TypeScript language server's analysis.
// Run with `npm run test:unit` (no VS Code instance required).
import * as assert from "assert";

import {
  computeDiagnostics,
  computeInlayHints,
  computeSemanticTokens,
  findLineCommentStart,
  inferType,
  SemanticToken,
} from "../../analysis";

function tokenText(source: string, token: SemanticToken): string {
  return source.split(/\r?\n/)[token.line]?.slice(token.start, token.start + token.length) ?? "";
}

suite("findLineCommentStart", () => {
  test("recognises both // and # comments", () => {
    assert.strictEqual(findLineCommentStart("proclaim 1; // note"), 12);
    assert.strictEqual(findLineCommentStart("proclaim 1; # note"), 12);
    assert.strictEqual(findLineCommentStart("# whole line"), 0);
  });

  test("ignores comment markers inside strings", () => {
    assert.strictEqual(findLineCommentStart('proclaim "a # b // c";'), -1);
    assert.strictEqual(findLineCommentStart('proclaim "esc \\" #"; # real'), 21);
  });
});

suite("computeDiagnostics", () => {
  test("flags typed inscribe mismatch on the type name", () => {
    const [diag] = computeDiagnostics('inscribe x: HolyInt = "text";');
    assert.ok(diag);
    assert.match(diag.message, /declared HolyInt but assigned Text/);
    assert.deepStrictEqual(diag.range, {
      start: { line: 0, character: 12 },
      end: { line: 0, character: 19 },
    });
  });

  test("ranges come from the match, not the first textual occurrence", () => {
    // `Text` first appears inside the variable name `Textile`.
    const [inscribeDiag] = computeDiagnostics("inscribe Textile: Text = 5;");
    assert.strictEqual(inscribeDiag?.range.start.character, 18);

    // `n` first appears inside the keyword `amend`.
    const source = 'inscribe n: HolyInt = 1;\namend n = "x";';
    const [amendDiag] = computeDiagnostics(source);
    assert.strictEqual(amendDiag?.range.start.line, 1);
    assert.strictEqual(amendDiag?.range.start.character, 6);
  });

  test("commented-out code produces no diagnostics", () => {
    assert.deepStrictEqual(computeDiagnostics('# inscribe x: HolyInt = "a";'), []);
    assert.deepStrictEqual(computeDiagnostics('// inscribe x: HolyInt = "a";'), []);
    assert.deepStrictEqual(computeDiagnostics('proclaim 1; # amend y = "a" - 1;'), []);
  });

  test("accepts compatible assignments", () => {
    assert.deepStrictEqual(computeDiagnostics("inscribe f: HolyFloat = 3;"), []);
    assert.deepStrictEqual(computeDiagnostics('inscribe s: String = "ok";'), []);
  });

  test("flags arithmetic on text", () => {
    const [diag] = computeDiagnostics('proclaim "a" - 1;');
    assert.match(diag?.message ?? "", /invalid operator/);
  });

  test("checks every statement on a line, not just the first", () => {
    const diags = computeDiagnostics('inscribe a: HolyInt = 1; inscribe b: HolyInt = "no";');
    assert.strictEqual(diags.length, 1);
    assert.strictEqual(diags[0]?.range.start.character, 37);

    const amends = computeDiagnostics(
      'inscribe a: HolyInt = 1; inscribe b: HolyInt = 2;\namend a = 3; amend b = "x";'
    );
    assert.strictEqual(amends.length, 1);
    assert.match(amends[0]?.message ?? "", /'b' is HolyInt/);
  });

  test("amend resolves the declaration visible in its own scope", () => {
    const source = [
      "mystery func_a() {",
      "  inscribe x: HolyInt = 5;",
      "} amen",
      "mystery func_b() {",
      '  inscribe x: Text = "word";',
      '  amend x = "hello";',
      "} amen",
    ].join("\n");
    assert.deepStrictEqual(computeDiagnostics(source), []);

    const wrong = source.replace('amend x = "hello";', "amend x = 1;");
    const [diag] = computeDiagnostics(wrong);
    assert.match(diag?.message ?? "", /'x' is Text but amended with HolyInt/);
  });

  test("typed parameters are declarations of the function body", () => {
    const source = 'mystery f(n: HolyInt) {\n  amend n = "x";\n} amen\namend n = "ok";';
    const diags = computeDiagnostics(source);
    assert.strictEqual(diags.length, 1);
    assert.strictEqual(diags[0]?.range.start.line, 1);
  });

  test("inner block shadow does not leak to outer amends", () => {
    const source = [
      "inscribe v: HolyInt = 1;",
      'discern (Verily) { inscribe v: Text = "s"; amend v = "t"; } otherwise { silence; } amen',
      "amend v = 2;",
    ].join("\n");
    assert.deepStrictEqual(computeDiagnostics(source), []);
  });
});

suite("computeSemanticTokens", () => {
  test("marks # comments as comments and keeps their contents un-tokenised", () => {
    const source = "proclaim 1; # inscribe x = 2;";
    const tokens = computeSemanticTokens(source);
    const comment = tokens.find((t) => t.tokenType === "comment");
    assert.strictEqual(comment && tokenText(source, comment), "# inscribe x = 2;");
    assert.ok(!tokens.some((t) => t.tokenType === "keyword" && t.start > 12));
  });

  test("declaration names are located by capture offset", () => {
    // `m` also occurs at the start of `mystery`.
    const source = "mystery m() { silence; } amen";
    const decl = computeSemanticTokens(source).find((t) => t.modifiers.includes("declaration"));
    assert.ok(decl);
    assert.strictEqual(decl.start, 8);
    assert.strictEqual(tokenText(source, decl), "m");
  });

  test("covers keywords missing before (as, is, not) and Mystery type", () => {
    const source = 'tradition "a.lg" as A; proclaim x is not y; inscribe z: Mystery = 1;';
    const texts = computeSemanticTokens(source).map((t) => `${t.tokenType}:${tokenText(source, t)}`);
    for (const expected of ["keyword:as", "keyword:is", "keyword:not", "type:Mystery"]) {
      assert.ok(texts.includes(expected), `missing ${expected} in ${texts.join(", ")}`);
    }
  });

  test("builtins get the defaultLibrary modifier", () => {
    const tokens = computeSemanticTokens("proclaim measure([1]);");
    const call = tokens.find((t) => t.tokenType === "function");
    assert.deepStrictEqual(call?.modifiers, ["defaultLibrary"]);
  });
});

suite("computeInlayHints / inferType", () => {
  test("hints untyped declarations right after the name", () => {
    const [hint] = computeInlayHints('inscribe greeting = "hi";', 0, 0);
    assert.strictEqual(hint?.label, ": Text");
    assert.deepStrictEqual(hint?.position, { line: 0, character: 17 });
  });

  test("no hint for typed declarations or commented lines", () => {
    assert.deepStrictEqual(computeInlayHints("inscribe x: HolyInt = 1;", 0, 0), []);
    assert.deepStrictEqual(computeInlayHints("# inscribe x = 1;", 0, 0), []);
  });

  test("does not guess a type for compound arithmetic", () => {
    assert.strictEqual(inferType("1 + 2.5"), null);
    assert.strictEqual(inferType('"a < b"'), "Text");
    assert.strictEqual(inferType("a is b"), "Bool");
  });

  test("indexing or combining processions is not itself a Procession", () => {
    assert.strictEqual(inferType("[1][0]"), null);
    assert.strictEqual(inferType("[1] + [2]"), null);
    assert.strictEqual(inferType("[1, [2, 3]]"), "Procession");
    assert.deepStrictEqual(computeDiagnostics("inscribe x: HolyInt = [1][0];"), []);
  });

  test("comparisons nested in calls, lists or icons do not make the whole expression Bool", () => {
    assert.strictEqual(inferType("choose(a < b, 1, 2)"), null);
    assert.strictEqual(inferType("[1 < 2]"), "Procession");
    assert.strictEqual(inferType("write Pair { ok = a < b }"), "Pair");
    assert.strictEqual(inferType("(a < b)"), "Bool");
    assert.strictEqual(inferType("(a) < (b)"), "Bool");
    assert.strictEqual(inferType("((1))"), "HolyInt");
    assert.strictEqual(inferType("f(x) < 3"), "Bool");
    assert.deepStrictEqual(computeDiagnostics("inscribe x: HolyInt = choose(a < b, 1, 2);"), []);
  });
});

suite("user icon types", () => {
  test("declared icon names are coloured as types where used", () => {
    const source = "icon Disciple { name: Text; } amen\ninscribe p: Disciple = write Disciple { name = \"A\" };";
    const types = computeSemanticTokens(source)
      .filter((t) => t.tokenType === "type" && tokenText(source, t) === "Disciple")
      .map((t) => `${t.line}:${t.start}`);
    assert.deepStrictEqual(types, ["0:5", "1:12", "1:29"]);
  });
});
