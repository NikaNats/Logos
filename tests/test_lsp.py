from __future__ import annotations

import importlib.util
import unittest
from dataclasses import dataclass
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
LSP_PATH = ROOT / "packages" / "logos-vscode" / "server" / "lsp_server.py"


def _load_lsp_module():
    spec = importlib.util.spec_from_file_location("logos_lsp_server", LSP_PATH)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"Failed to load module spec from {LSP_PATH}")
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


@dataclass
class _Doc:
    source: str


class _Workspace:
    def __init__(self, text: str):
        self._doc = _Doc(text)

    def get_document(self, uri: str) -> _Doc:
        return self._doc


class _LS:
    def __init__(self, text: str):
        self.workspace = _Workspace(text)
        self.published: dict[str, list[object]] = {}

    def publish_diagnostics(self, uri: str, diagnostics: list[object]) -> None:
        self.published[uri] = diagnostics


class LspTests(unittest.TestCase):
    def test_lsp_tolerates_incomplete_code(self) -> None:
        lsp = _load_lsp_module()
        ls = _LS("mystery main() { inscribe")
        lsp.validate(ls, "file:///test.lg")
        diags = ls.published.get("file:///test.lg", [])
        self.assertGreaterEqual(len(diags), 1)

    def test_lsp_reports_literal_type_mismatch(self) -> None:
        lsp = _load_lsp_module()
        src = 'mystery main() { inscribe x: HolyInt = "no"; } amen'
        tree = lsp.PARSER.parse(src)
        diags = lsp._typecheck(tree)
        self.assertTrue(any("Type mismatch" in d.message for d in diags))

    def test_lsp_reports_call_argument_type_mismatch(self) -> None:
        lsp = _load_lsp_module()
        src = (ROOT / "tests" / "fixtures" / "lsp_fail_call_arg_type.lg").read_text(
            encoding="utf-8"
        )
        tree = lsp.PARSER.parse(src)
        diags = lsp._typecheck(tree)
        self.assertTrue(any("call 'id'" in d.message for d in diags))

    def test_lsp_reports_return_type_mismatch_on_assignment(self) -> None:
        lsp = _load_lsp_module()
        src = (
            ROOT / "tests" / "fixtures" / "lsp_fail_return_type_assignment.lg"
        ).read_text(encoding="utf-8")
        tree = lsp.PARSER.parse(src)
        diags = lsp._typecheck(tree)
        self.assertTrue(any("declared Text" in d.message for d in diags))

    def test_lsp_reports_amend_expression_type_mismatch(self) -> None:
        lsp = _load_lsp_module()
        src = (ROOT / "tests" / "fixtures" / "lsp_fail_amend_expr_type.lg").read_text(
            encoding="utf-8"
        )
        tree = lsp.PARSER.parse(src)
        diags = lsp._typecheck(tree)
        self.assertTrue(
            any("cannot add" in d.message or "amended" in d.message for d in diags)
        )

    def test_lsp_reports_non_numeric_operator_mismatch(self) -> None:
        lsp = _load_lsp_module()
        src = (ROOT / "tests" / "fixtures" / "lsp_fail_non_numeric_op.lg").read_text(
            encoding="utf-8"
        )
        tree = lsp.PARSER.parse(src)
        diags = lsp._typecheck(tree)
        self.assertTrue(any("cannot subtract" in d.message for d in diags))

    def test_lsp_respects_function_scopes_for_shadowing(self) -> None:
        lsp = _load_lsp_module()
        src = (ROOT / "tests" / "fixtures" / "lsp_scope_shadowing.lg").read_text(
            encoding="utf-8"
        )
        tree = lsp.PARSER.parse(src)
        diags = lsp._typecheck(tree)
        # func_b has x: Text, so x + 1 should be flagged.
        self.assertTrue(any("cannot add Text" in d.message for d in diags))

    def test_lsp_warns_on_unreachable_code_after_offer(self) -> None:
        lsp = _load_lsp_module()
        src = (
            ROOT / "tests" / "fixtures" / "lsp_unreachable_after_offer.lg"
        ).read_text(encoding="utf-8")
        tree = lsp.PARSER.parse(src)
        diags = lsp._typecheck(tree)
        self.assertTrue(any("Unreachable code" in d.message for d in diags))


if __name__ == "__main__":  # pragma: no cover
    unittest.main(verbosity=2)
