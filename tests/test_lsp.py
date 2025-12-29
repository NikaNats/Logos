from __future__ import annotations

import importlib.util
import unittest
from dataclasses import dataclass
from pathlib import Path
from lark import Lark

# Import grammar from library for test validation
from logos_lang import LOGOS_GRAMMAR

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
    def setUp(self):
        self.lsp = _load_lsp_module()
        # Ensure the test grammar matches the library grammar
        self.parser = Lark(LOGOS_GRAMMAR, parser="lalr")

    def test_lsp_reports_literal_type_mismatch(self) -> None:
        src = 'mystery main() { inscribe x: HolyInt = "no"; } amen'
        tree = self.parser.parse(src)
        diags = self.lsp._typecheck(tree)
        self.assertTrue(any("Type mismatch" in d.message for d in diags))

    def test_lsp_reports_call_argument_type_mismatch(self) -> None:
        src = (ROOT / "tests" / "fixtures" / "lsp_fail_call_arg_type.lg").read_text(
            encoding="utf-8"
        )
        tree = self.parser.parse(src)
        diags = self.lsp._typecheck(tree)
        self.assertTrue(any("call 'id'" in d.message for d in diags))

    def test_lsp_reports_return_type_mismatch_on_assignment(self) -> None:
        src = (
            ROOT / "tests" / "fixtures" / "lsp_fail_return_type_assignment.lg"
        ).read_text(encoding="utf-8")
        tree = self.parser.parse(src)
        diags = self.lsp._typecheck(tree)
        self.assertTrue(any("declared Text" in d.message for d in diags))

    def test_lsp_warns_on_unreachable_code_after_offer(self) -> None:
        src = (
            ROOT / "tests" / "fixtures" / "lsp_unreachable_after_offer.lg"
        ).read_text(encoding="utf-8")
        tree = self.parser.parse(src)
        diags = self.lsp._typecheck(tree)
        self.assertTrue(any("Unreachable code" in d.message for d in diags))


if __name__ == "__main__":
    unittest.main(verbosity=2)
