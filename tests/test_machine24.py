"""Construction checks and negative controls for the 24-state replacement."""
import sys
from pathlib import Path
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]/'tools'))
from machine import Config, load_lean, check_prime
from verify24 import bootstrap, construction, check_growth, check_pair


class Machine24Tests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.machine = construction()

    def test_exact_state_count_and_only_changed_edge(self):
        self.assertEqual(len(self.machine), 24)
        self.assertEqual(self.machine[0][0], (0, 1, 10))
        self.assertIsNone(self.machine[23][0])

    def test_blank_bootstrap(self):
        bootstrap(self.machine)

    def test_general_growth_including_empty_right_block(self):
        for p, q in ((1,0),(1,1),(2,0),(2,2),(7,0),(7,9),(31,32)):
            check_growth(self.machine, p, q)

    def test_growth_needs_correct_entry(self):
        wrong = list(self.machine)
        wrong[0] = ((1, 1, 10), wrong[0][1])
        with self.assertRaises(AssertionError):
            check_growth(tuple(wrong), 3, 4)

    def test_first_pair_boundary(self):
        for p, q in ((2,2),(3,3),(4,4),(3,9),(9,3),(9,9),(1,3)):
            check_pair(self.machine, p, q)

    def test_unmodified_prime_interface(self):
        for n in (1,2,3,4,5,9,17,25):
            check_prime(self.machine, n, (1,0,1), (1,1,0,1))

    def test_original_machine_also_satisfies_pair_contract(self):
        original = load_lean()
        for p, q in ((2,2),(3,3),(4,4),(3,9),(9,3)):
            check_pair(original, p, q)

    def test_corrupted_composite_pair_rejected(self):
        wrong = tuple(tuple(None if e is None else (e[0], e[1], 20 if e[2] == 16 else e[2])
                            for e in row) for row in self.machine)
        with self.assertRaises(AssertionError):
            check_pair(tuple(wrong), 4, 4, limit=10000)


if __name__ == '__main__':
    unittest.main()
