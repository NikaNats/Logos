import sys
import time
import unittest

from tests.canon_runner import _execute_fixture


class StressTests(unittest.TestCase):
    def test_tco_performance_100k_iterations(self) -> None:
        start_time = time.perf_counter()
        result = _execute_fixture("stress/tco_deep_100k.lg", env={"LOGOS_MAX_TCO": "200000"})
        duration = time.perf_counter() - start_time

        # Correctness is always asserted; the wall-clock budget is meaningless while a
        # tracer (coverage, debugger) slows every Python call several-fold.
        self.assertIsNone(result.error)
        if sys.gettrace() is not None or sys.monitoring.get_tool(sys.monitoring.COVERAGE_ID):
            self.skipTest("timing budget not enforced under a tracer")
        self.assertLess(duration, 2.0, "The liturgy is too slow; the monks are falling asleep.")


if __name__ == "__main__":  # pragma: no cover
    unittest.main(verbosity=2)
