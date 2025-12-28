import unittest

import pytest

pytest_lsp = pytest.importorskip("pytest_lsp")


class LspProtocolSmokeTests(unittest.TestCase):
    @pytest.mark.skip("Protocol exercise requires pytest-lsp wiring; placeholder for future integration.")
    def test_protocol_placeholder(self) -> None:  # pragma: no cover
        assert True


if __name__ == "__main__":  # pragma: no cover
    unittest.main(verbosity=2)
