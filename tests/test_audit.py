"""Audit mechanics, including deliberate corruption and halting fixtures."""
import copy
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
from audit import check_certificate, collapse, conflicts, observe, tape_windows
from machine import Config, SOURCE, check_outer, check_prime, format_machine, load_lean


class AuditTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.machine = load_lean()
        cls.masks, cls.first = observe(cls.machine, 853)
        cls.certificate = conflicts(cls.machine, cls.masks)

    def test_exact_table(self):
        self.assertEqual(len(self.machine), 25)
        self.assertEqual(self.machine[0], ((1, 1, 22), (1, 1, 1)))
        self.assertEqual(self.machine[24], (None, (1, 1, 23)))
        self.assertEqual(len(format_machine(self.machine).splitlines()), 25)

    def test_parser_rejects_missing_transition(self):
        data = SOURCE.read_text()
        line = next(s for s in data.splitlines() if s.startswith('| ⟨24, _⟩, Γ.zero'))
        with tempfile.TemporaryDirectory() as d:
            p = Path(d)/'bad.lean'
            p.write_text(data.replace(line, ''))
            with self.assertRaises(ValueError):
                load_lean(p)

    def test_halt_has_no_write_or_move(self):
        cfg = Config(24, 7, {0, 1})
        cfg.advance(self.machine)
        self.assertEqual((cfg.state, cfg.head, cfg.ones), (None, 7, {0, 1}))

    def test_all_working_branches_and_all_pairs(self):
        self.assertEqual(len(self.first), 49)
        self.assertNotIn('24:0', self.first)
        self.assertEqual(check_certificate(self.machine, self.first, self.certificate), 300)

    def test_bad_reachability_witness_rejected(self):
        wrong = dict(self.first)
        wrong['0:0'] = 1
        with self.assertRaises(AssertionError):
            check_certificate(self.machine, wrong, self.certificate)

    def test_bad_successor_certificate_rejected(self):
        wrong = copy.deepcopy(self.certificate)
        item = next(x for x in wrong if x['kind'] == 'successor')
        item['pair_dependency'] = [0, 0]
        with self.assertRaises(AssertionError):
            check_certificate(self.machine, self.first, wrong)

    def test_identical_states_remain_compatible(self):
        toy = (((0, 1, 0), (1, 1, 0)), ((0, 1, 0), (1, 1, 0)))
        self.assertEqual(conflicts(toy, [3, 3]), [])

    def test_positive_macro_and_changed_context_rejection(self):
        toy = (((0, 1, 1), (1, 1, 1)), ((0, -1, 2), (1, -1, 2)),
               ((0, 1, 3), (1, 1, 3)), (None, None))
        self.assertEqual(collapse(toy, 0, 0, 3), (0, 1, 3))
        self.assertEqual(collapse(toy, 0, 1, 3), (1, 1, 3))
        bad = list(toy)
        bad[1] = ((1, -1, 2), (1, -1, 2))
        self.assertIsNone(collapse(tuple(bad), 0, 0, 3))
        self.assertIsNone(collapse(toy, 0, 0, 5))

    def test_window_contains_witnessed_branches(self):
        found = tape_windows(self.machine, 3)
        self.assertTrue(all((observed & allowed) == observed for observed, allowed in
                            zip(self.masks, found['possible_read_masks'])))

    def test_prime_boundaries_preserve_context(self):
        for n in (1, 2, 3, 4, 9, 17, 25):
            check_prime(self.machine, n, (1, 0, 1), (1, 1, 0, 1))

    def test_positive_and_synthetic_halting_outer_cases(self):
        self.assertEqual(check_outer(self.machine, 12)['outcome'], 'next_even')
        self.assertEqual(check_outer(self.machine, 11)['outcome'], 'halt')

    def test_corrupted_primality_rejected(self):
        wrong = list(self.machine)
        wrong[2] = ((0, -1, 16), wrong[2][1])  # incorrectly calls 2 composite
        with self.assertRaises(AssertionError):
            check_prime(tuple(wrong), 2)


if __name__ == '__main__':
    unittest.main()
