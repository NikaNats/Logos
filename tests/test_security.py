import unittest

from tests.canon_runner import _execute_fixture


class SecurityTests(unittest.TestCase):
    def test_sandbox_escape_is_prevented(self) -> None:
        result = _execute_fixture("security/reflection_attack.lg")
        self.assertNotIn("HERESY", result.stdout)
        # Either the vigil handler prints a denial or the interpreter raises a forbidden-access error.
        if result.stdout:
            self.assertIn("Access denied", result.stdout)
        else:
            self.assertIsNotNone(result.error)
            self.assertIn("forbidden", str(result.error).lower())

    def test_path_traversal_blocked(self) -> None:
        result = _execute_fixture("security/path_traversal_blocked.lg")
        self.assertIsNone(result.error)
        self.assertIn("0", result.stdout)

    def test_private_attribute_blocked(self) -> None:
        result = _execute_fixture("security/private_attr_block.lg")
        self.assertIsNone(result.error)
        self.assertIn("Denied", result.stdout)


if __name__ == "__main__":  # pragma: no cover
    unittest.main(verbosity=2)
