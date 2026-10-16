"""Adversarial checks of the native search screen against literal TM behavior."""
import ctypes
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]/'tools'))
from machine import ROOT, check_prime, check_outer
from verify24 import construction, check_pair
from search_scans import inputs
from search23 import encode, load_screen
from search23 import diagnostics, outer_fixture


@unittest.skipUnless(shutil.which('clang++') or shutil.which('g++'), 'Needs a C++17 compiler')
class SearchScreenTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.directory = tempfile.TemporaryDirectory(prefix='goldbach-screen-test-')
        cls.addClassCleanup(cls.directory.cleanup)
        cls.library = Path(cls.directory.name)/'screen.so'
        compiler = shutil.which('clang++') or shutil.which('g++')
        subprocess.run([compiler, '-std=c++17', '-O2', '-DSCREEN_LIBRARY', '-shared',
                        '-fPIC', str(ROOT/'tools/search23.cpp'), '-o', str(cls.library)], check=True)
        cls.machine = construction()
        cls.broad_library = Path(cls.directory.name)/'broad-screen.so'
        subprocess.run([compiler, '-std=c++17', '-O2', '-DSCREEN_LIBRARY', '-shared',
                        '-fPIC', '-DBOOTSTRAP_STEPS=1000000', '-DBOOTSTRAP_MAX_EVEN=256',
                        '-DBOOTSTRAP_TAPE=32768', '-DBOOTSTRAP_MAX_ONES=2048',
                        str(ROOT/'tools/search23.cpp'), '-o', str(cls.broad_library)], check=True)

    def screen(self, machine, fixtures):
        lib = load_screen(self.library, fixtures)
        data = [encode(edge or (0,0,-1)) for row in machine for edge in row]
        trace = ctypes.c_uint64()
        status = lib.check((ctypes.c_int*48)(*data), -1, -1, ctypes.byref(trace))
        return status, trace.value, lib.last_steps()

    def changed(self, replacements):
        return tuple(tuple(replacements.get((q,b), edge) for b, edge in enumerate(row))
                     for q, row in enumerate(self.machine))

    def test_current_machine_passes_all_fixtures_and_bootstraps(self):
        fixtures = [list(map(int, line.split())) for line in inputs(self.machine).splitlines()[49:]]
        status, start, steps = self.screen(self.machine, fixtures)
        self.assertEqual((status, start), (-1, 18))
        self.assertGreater(steps, 0)

    def test_later_even_blank_boundary_is_optional_and_exact(self):
        # From this fixed initial state the first and only boundary has ten
        # ones. Broader initialization accepts it; the legacy bound does not.
        toy = [[[0,0,-1] for _ in range(2)] for _ in range(24)]
        for q in range(10):
            toy[q][0] = [1,1,q+1 if q < 9 else 21]
        data = (ctypes.c_int*48)(*[encode(e) for row in toy for e in row])
        def blank(library, table):
            lib = ctypes.CDLL(str(library))
            lib.check_blank.argtypes = [ctypes.POINTER(ctypes.c_int), ctypes.c_int,
                                       ctypes.c_int, ctypes.c_int]
            lib.check_blank.restype = ctypes.c_int
            return lib.check_blank(table, -1, -1, 0)
        self.assertEqual(blank(self.library, data), 0)
        self.assertEqual(blank(self.broad_library, data), 1)
        toy[4][0] = [0,1,5]  # A hole leaves an odd count and no unary boundary.
        damaged = (ctypes.c_int*48)(*[encode(e) for row in toy for e in row])
        self.assertEqual(blank(self.broad_library, damaged), 0)

    def test_whole_phase_fixtures_include_odd_successes_and_failures(self):
        self.assertEqual(outer_fixture(self.machine, 5)[:4], (1,5,0,1))
        self.assertEqual(outer_fixture(self.machine, 11)[:4], (1,11,0,0))

    def test_original_machine_passes_proposal_diagnostics(self):
        table = [[e or (0,0,-1) for e in row] for row in self.machine]
        report = diagnostics(table)
        self.assertTrue(all(not suite['failed'] for suite in report.values()))

    def test_even_always_advance_proposal_retains_failure_diagnostics(self):
        # This advances every outer input by two, including no-pair odd inputs.
        # Even examples pass, but that supplies no unbounded arithmetic proof.
        m = self.changed({(21,0):(1,1,0), (0,0):(1,1,21)})
        self.assertEqual(outer_fixture(m, 128)[:4], (1,128,0,1))
        report = diagnostics([[e or (0,0,-1) for e in row] for row in m])
        self.assertTrue(report['original_pair_interface']['failed'])
        self.assertTrue(any(f['input'] == 11 for f in report['odd_outer_domain']['failed']))

    def test_repair_search_recovers_known_toy_quotient(self):
        # A four-step blank bootstrap plus a one-step nonprime return. Merging
        # 0 into 1 breaks that return; one repaired edge and starting in 4 recover
        # both contracts. This checks the search itself has a positive control.
        toy = [[[0,0,-1] for _ in range(2)] for _ in range(24)]
        for q, target in ((0,1),(1,2),(2,3),(3,21),(4,0)):
            toy[q][0] = [1,1,target]
        toy[0][1] = [1,-1,16]
        data = '\n'.join(' '.join(map(str,e)) for row in toy for e in row)
        data += '\n1 2\n2 1 0 0 1\n1 11 0 0 1\n'
        compiler = shutil.which('clang++') or shutil.which('g++')
        executable = Path(self.directory.name)/'repair-test'
        subprocess.run([compiler, '-std=c++17', '-O2', str(ROOT/'tools/search23.cpp'),
                        '-o', str(executable)], check=True)
        output = Path(self.directory.name)/'toy-results'
        output.mkdir()
        subprocess.run([str(executable), str(output), '1', 'all'], input=data,
                       text=True, stdout=subprocess.DEVNULL, check=True)
        candidates = [json.loads(path.read_text()) for path in output.glob('candidate-*.json')]
        self.assertTrue(any(c['removed'] == 0 and c['merged_into'] == 1 and
                            c['start'] == 4 and c['table'][1][1] == [1,-1,16]
                            for c in candidates))

    def test_bad_prime_return_cannot_be_repaired_later(self):
        # At step 1 this enters prime exit 20 on an erased tape. At step 5 it
        # returns to composite exit 16 with the original tape. Only the first
        # return is admissible; the former native checker accepted the later one.
        m = self.changed({(0,1):(0,-1,20), (20,0):(1,1,18), (18,0):(1,-1,19),
                          (19,1):(0,1,22), (22,1):(1,-1,16)})
        with self.assertRaises(AssertionError):
            check_prime(m, 1)
        self.assertEqual(self.screen(m, [(2,1,0,False,3)]), (0, 1 << 1, 1))

    def test_classification_only_contract_allows_changed_return_tape(self):
        m = self.changed({(0,1):(0,-1,16)})
        self.assertEqual(self.screen(m, [(2,1,0,False,3)])[0], 0)
        self.assertEqual(self.screen(m, [(4,1,0,False,3)])[:2], (-1,18))

    def test_first_pair_return_with_wrong_number_is_rejected(self):
        m = self.changed({(17,1):(1,-1,16), (16,0):(1,1,17)})
        with self.assertRaisesRegex(AssertionError, 'wrong next pair'):
            check_pair(m, 2, 2, limit=4)
        status, _, steps = self.screen(m, [(3,2,2,True,65)])
        self.assertEqual((status, steps), (0, 4))

    def test_first_outer_return_with_wrong_number_is_rejected(self):
        # This fake machine increments by one twice. It must not be accepted
        # merely because its second boundary happens to contain the wanted n+2.
        m = self.changed({(21,0):(1,1,21)})
        with self.assertRaisesRegex(AssertionError, 'wrong first outer boundary'):
            check_outer(m, 4)
        status, _, steps = self.screen(m, [(1,4,0,True,73)])
        self.assertEqual((status, steps), (0, 1))

    def test_deleted_halting_branch_fails_negative_fixture(self):
        m = self.changed({(23,0):(0,-1,0)})
        status, _, _ = self.screen(m, [(1,11,0,False,1099)])
        self.assertEqual(status, 0)

    def test_actual_halt_passes_negative_fixture(self):
        status, start, _ = self.screen(self.machine, [(1,11,0,False,1099)])
        self.assertEqual((status, start), (-1, 18))


if __name__ == '__main__':
    unittest.main()
