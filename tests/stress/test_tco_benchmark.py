import time
import unittest

from tests.canon_runner import _execute_fixture


class StressTests(unittest.TestCase):
    def test_tco_performance_100k_iterations(self) -> None:
        start_time = time.time()
        result = _execute_fixture("stress/tco_deep_100k.lg", env={"LOGOS_MAX_TCO": "200000"})
        duration = time.time() - start_time

        self.assertIsNone(result.error)
        self.assertLess(duration, 2.0, "The liturgy is too slow; the monks are falling asleep.")


if __name__ == "__main__":  # pragma: no cover
    unittest.main(verbosity=2)
