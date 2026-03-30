import * as assert from "assert";
import * as vscode from "vscode";
import { suite, test } from "mocha";

suite("Logos Extension Host", () => {
  test("Logos language is registered", async () => {
    const languages = await vscode.languages.getLanguages();
    assert.ok(languages.includes("logos"));
  });

  test("Logos extension activates", async () => {
    const extension = vscode.extensions.getExtension("Theophilus.logos-lang");
    if (!extension) {
      // In development host runs the local extension; absence here indicates misconfigured test env.
      assert.fail("Extension Theophilus.logos-lang was not discovered in host");
    }
    if (!extension.isActive) {
      await extension.activate();
    }
    assert.ok(extension.isActive);
  });
});
