import unittest
from pathlib import Path
from unittest.mock import patch

from run_exact_batch import GIB, memory_allows_start, source_priority


class ExactBatchSchedulingTests(unittest.TestCase):
    def test_memory_gate_accounts_for_pending_workers(self):
        with patch("run_exact_batch.cgroup_memory", return_value=(64 * GIB, 30 * GIB)):
            self.assertTrue(memory_allows_start(16, 8, active_jobs=0))
            self.assertTrue(memory_allows_start(16, 8, active_jobs=1))
            self.assertFalse(memory_allows_start(16, 8, active_jobs=2))

    def test_memory_gate_can_be_disabled(self):
        with patch("run_exact_batch.cgroup_memory", return_value=(64 * GIB, 64 * GIB)):
            self.assertTrue(memory_allows_start(16, 0, active_jobs=16))

    def test_smaller_expected_sat_problem_runs_first(self):
        easy = Path("Code_288_32_10_l12m12_1.lean")
        hard = Path("Code_360_32_20_l15m12_2.lean")
        self.assertLess(source_priority(easy), source_priority(hard))

    def test_unknown_name_runs_last(self):
        known = Path("Code_360_32_20_l15m12_2.lean")
        unknown = Path("Code_custom.lean")
        self.assertLess(source_priority(known), source_priority(unknown))


if __name__ == "__main__":
    unittest.main()
