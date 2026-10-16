"""Search for 23 states by merging two states and repairing transitions.

Finite phase contracts and finite execution bounds only: neither failure nor
solver UNSAT is a lower bound on equivalent Turing machines. The default mode
uses a C++17 compiler. The optional solver mode also needs z3-solver.
"""
import argparse
import ctypes
import hashlib
import json
from pathlib import Path
import random
import shutil
import subprocess
import sys
import tempfile

from machine import ROOT, Config, check_prime, goldbach, load_lean
from verify24 import CURRENT_SOURCE, check_pair
from search_scans import inputs

SCAN_GROUPS = ((13,14,16,18,20,22), (11,19,21), (5,7,8))


def outer_fixture(machine, n, limit=5_000_000):
    """Include odd successes as well as odd failures in a whole-phase search."""
    success = goldbach(n)
    cfg = Config(21, n, set(range(n)))
    for steps in range(1, limit+1):
        cfg.advance(machine)
        if cfg.state is None:
            assert not success, (n, 'unexpected baseline halt')
            return (1, n, 0, 0, steps)
        if cfg.state == 21 and cfg.ones and cfg.head not in cfg.ones and cfg.ones == set(range(cfg.head-len(cfg.ones), cfg.head)):
            assert success and len(cfg.ones) == n+2, (n, 'wrong baseline return')
            return (1, n, 0, 1, steps)
    raise ValueError(f'Baseline outer fixture {n} exceeded the step budget')


def diagnostics(table):
    """Record original-interface behavior without imposing it on a new machine."""
    machine = tuple(tuple(None if e[2] < 0 else tuple(e) for e in row) for row in table)
    result = {}
    suites = {
        'original_primality_interface': [(n, lambda n=n: check_prime(machine, n, limit=20_000))
                                         for n in (1,2,3,4,5,7,9,11,15)],
        'original_pair_interface': [(list(pq), lambda p=pq[0], q=pq[1]:
                                    check_pair(machine, p, q, limit=50_000))
                                   for pq in ((2,2),(4,4),(3,3),(5,3),(3,5),(4,2),(2,4),(6,6),(9,3),(3,9))],
        'odd_outer_domain': [(n, lambda n=n: outer_fixture(machine, n, limit=50_000))
                             for n in (5,9,11,17,23,27)]}
    for name, checks in suites.items():
        passed, failed = [], []
        for case, check in checks:
            try:
                check()
                passed.append(case)
            except (AssertionError, ValueError) as error:
                failed.append({'input': case, 'failure': str(error)})
        result[name] = {'passed': passed, 'failed': failed}
    return result


def encode(edge):
    w, d, q = edge
    return 0 if q < 0 else 1 + 4*q + 2*w + int(d > 0)


def decode(value):
    return [0, 0, -1] if not value else [((value-1) % 4)//2,
            1 if (value-1) % 2 else -1, (value-1)//4]


def load_screen(library, fixtures):
    """Load the native checker; the returned failure trace is an exact branch set."""
    lib = ctypes.CDLL(str(library))
    integer, trace = ctypes.c_int, ctypes.c_uint64
    lib.initialize.argtypes = [ctypes.POINTER(integer), integer]
    lib.initialize.restype = None
    lib.check.argtypes = [ctypes.POINTER(integer), integer, integer, ctypes.POINTER(trace)]
    lib.check.restype = integer
    lib.last_steps.restype = ctypes.c_longlong
    lib.initialize((integer*(5*len(fixtures)))(*[v for f in fixtures for v in f]), len(fixtures))
    return lib


def solver_search(args, library, data):
    try:
        import z3
    except ImportError:
        raise SystemExit('Solver mode requires the optional z3-solver Python package')
    lines = data.splitlines()
    baseline = [list(map(int, line.split())) for line in lines[:48]]
    fixtures = [list(map(int, line.split())) for line in lines[49:]]
    lib = load_screen(library, fixtures)
    groups = SCAN_GROUPS if args.groups == 'scans' else (tuple(range(24)),)
    pairs = (args.merge_pair or
             [(d,k) for group in groups for d in group for k in group if d != k])
    random.Random(args.seed).shuffle(pairs)
    report = {'method': 'counterexample_guided_solver', 'z3': z3.get_version_string(),
              'repairs': args.repairs, 'seed': args.seed, 'pairs': [], 'finite_survivors': 0}
    for dead, keep in pairs:
        old = [encode([w,d,keep if q == dead else q]) for w,d,q in baseline]
        solver = z3.Solver()
        solver.set(timeout=2000, max_memory=768, random_seed=args.seed)
        edges = [z3.Int(f'e{i}') for i in range(48)]
        active = [i for i in range(48) if i//2 != dead]
        mutable = [i for i in active if args.editable_states is None or i//2 in args.editable_states]
        for i in active:
            solver.add(edges[i] >= 0, edges[i] <= 96,
                       z3.Or(edges[i] < 1+4*dead, edges[i] >= 5+4*dead))
        for i in range(48):
            if i not in mutable:
                solver.add(edges[i] == old[i])
        for q, b, w, move, target in args.fixed_edge or []:
            solver.add(edges[2*q+b] == encode((w, move, target)))
        if mutable:
            solver.add(z3.PbLe([(edges[i] != old[i], 1) for i in mutable], args.repairs))
        # A machine with no halting transition cannot pass the negative fixtures.
        solver.add(z3.Or([edges[i] == 0 for i in active]))
        result = {'removed': dead, 'merged_into': keep, 'checks': 0, 'status': 'budget', 'finite_survivors': 0,
                  'furthest_fixture': 0, 'bootstrap_rejections': 0}
        for _ in range(args.iterations):
            answer = solver.check()
            if answer != z3.sat:
                result['status'] = str(answer)
                if answer == z3.unknown:
                    result['reason'] = solver.reason_unknown()
                break
            model = solver.model()
            values = [model.eval(e).as_long() for e in edges]
            trace = ctypes.c_uint64()
            failed = lib.check((ctypes.c_int*48)(*values), dead, keep, ctypes.byref(trace))
            result['checks'] += 1
            if failed >= 0:
                if args.save_frontier and failed > result['furthest_fixture']:
                    frontier = {'removed': dead, 'merged_into': keep,
                                'first_failed_fixture': fixtures[failed] if failed < len(fixtures) else 'bootstrap',
                                'passed_fixture_prefix': failed, 'proof_status': 'unproved',
                                'table': [[decode(values[2*q]), decode(values[2*q+1])] for q in range(24)]}
                    (args.output/f'frontier-{dead}-{keep}.json').write_text(json.dumps(frontier, indent=2)+'\n')
                result['furthest_fixture'] = max(result['furthest_fixture'], failed)
                result['bootstrap_rejections'] += int(failed == len(fixtures))
            if failed < 0:
                result['status'] = 'finite_survivor'
                report['finite_survivors'] += 1
                result['finite_survivors'] += 1
                candidate = {'removed': dead, 'merged_into': keep, 'start': trace.value,
                             'even_outer_only': args.even_only, 'proof_status': 'unproved',
                             'table': [[decode(values[2*q]), decode(values[2*q+1])]
                                       for q in range(24)]}
                candidate['interface_diagnostics'] = diagnostics(candidate['table'])
                (args.output/f'candidate-{report["finite_survivors"]}.json').write_text(
                    json.dumps(candidate, indent=2)+'\n')
                if (report['finite_survivors'] >= args.max_survivors or
                        result['finite_survivors'] >= args.survivors_per_pair):
                    break
                solver.add(z3.Or([edges[i] != values[i] for i in mutable]))
                continue
            # Every table agreeing on these visited edges repeats this failure.
            # In the bootstrap case the trace covers every possible initial state.
            solver.add(z3.Or([edges[i] != values[i] for i in active if trace.value >> i & 1]))
        report['pairs'].append(result)
        (args.output/'summary.json').write_text(json.dumps(report, indent=2)+'\n')
        print(f'{dead} -> {keep}: {result["status"]}, {result["checks"]} checked tables', flush=True)
        if report['finite_survivors'] >= args.max_survivors:
            break


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=ROOT/'scratch/search23')
    parser.add_argument('--method', choices=('repair','solver'), default='repair')
    parser.add_argument('--repairs', type=int, help='Default: 1 for repair, 4 for solver')
    parser.add_argument('--groups', choices=('scans','all'), default='scans')
    parser.add_argument('--merge-pair', type=int, nargs=2, action='append', metavar=('DEAD','KEEP'),
                        help='Solver only: choose explicit state pairs instead of a scan group')
    parser.add_argument('--editable-states', type=lambda s: set(map(int, s.split(','))),
                        help='Solver only: freely synthesize just these rows, plus redirected incoming edges')
    parser.add_argument('--fixed-edge', type=int, nargs=5, action='append', metavar=('STATE','BIT','WRITE','MOVE','TARGET'),
                        help='Solver only: impose an edge from a structural template')
    contract = parser.add_mutually_exclusive_group()
    contract.add_argument('--pairs-only', action='store_true', help='Allow changes to the internal primality interface')
    contract.add_argument('--whole-phase-only', action='store_true',
                          help='Allow changes to both primality and pair interfaces; require outer phase behavior')
    parser.add_argument('--phase-factor', type=int, default=3,
                        help='Multiply the baseline step budget for each arithmetic fixture')
    parser.add_argument('--outer-through', type=int, default=0,
                        help='Add every whole-phase input from 4 through this value, including odd successes')
    parser.add_argument('--even-only', action='store_true',
                        help='Whole-phase mode: require arithmetic behavior only on the reachable even domain')
    parser.add_argument('--save-frontier', action='store_true', help='Solver: retain the longest passing fixture prefix per pair')
    parser.add_argument('--max-survivors', type=int, default=1, help='Solver: retain this many finite proposals for proof review')
    parser.add_argument('--survivors-per-pair', type=int, default=1, help='Solver: finite proposal limit for each merged pair')
    parser.add_argument('--odd-classification', action='store_true',
                        help='Whole-phase mode: add odd/2 primality-result checks with free return tape and left head position')
    parser.add_argument('--classification-offset', type=int, default=-1,
                        help='Rightmost allowed classification return head, relative to the first input cell')
    parser.add_argument('--success-certificates', action='store_true',
                        help='Guide whole-phase synthesis by requiring tested prime inputs whose sum is the outer input')
    parser.add_argument('--iterations', type=int, default=10000, help='Solver candidate budget per ordered state pair')
    parser.add_argument('--seed', type=int, default=2423)
    parser.add_argument('--bootstrap-steps', type=int, default=235)
    parser.add_argument('--bootstrap-max-even', type=int, default=4,
                        help='Permit any even outer boundary from 4 through this value')
    parser.add_argument('--bootstrap-tape', type=int, default=1024)
    parser.add_argument('--bootstrap-max-ones', type=int, default=12)
    args = parser.parse_args()
    args.repairs = args.repairs if args.repairs is not None else (1 if args.method == 'repair' else 4)
    if (not 1 <= args.repairs <= (2 if args.method == 'repair' else 46) or args.iterations < 1 or
            args.max_survivors < 1 or args.survivors_per_pair < 1):
        parser.error('Invalid repair count or solver candidate budget')
    if (args.merge_pair or args.fixed_edge or args.editable_states is not None) and args.method != 'solver':
        parser.error('Explicit merge pairs and editable rows require solver mode')
    if any(not 0 <= q < 24 for pair in args.merge_pair or [] for q in pair) or any(
            d == k for d,k in args.merge_pair or []):
        parser.error('Invalid merge pair')
    if args.editable_states is not None and (not args.editable_states or any(
            not 0 <= q < 24 for q in args.editable_states)):
        parser.error('Invalid editable states')
    if any(not (0 <= q < 24 and b in (0,1) and w in (0,1) and move in (-1,1) and -1 <= target < 24)
           for q,b,w,move,target in args.fixed_edge or []):
        parser.error('Invalid fixed edge')
    if args.even_only and not (args.whole_phase_only or args.pairs_only):
        parser.error('--even-only requires --whole-phase-only or --pairs-only')
    if args.odd_classification and not (args.whole_phase_only or args.pairs_only):
        parser.error('--odd-classification requires --whole-phase-only or --pairs-only')
    if (not -128 <= args.classification_offset <= 128 or args.phase_factor < 1 or args.bootstrap_steps < 1 or args.bootstrap_max_even < 4 or
            args.bootstrap_max_even % 2 or args.bootstrap_tape < 16 or
            args.bootstrap_max_ones < args.bootstrap_max_even):
        parser.error('Invalid bootstrap limits')
    compiler = shutil.which('clang++') or shutil.which('g++')
    if compiler is None:
        parser.error('A C++17 compiler is required')
    args.output.mkdir(parents=True, exist_ok=True)
    if any(args.output.iterdir()):
        parser.error('Output directory must be empty')
    machine = load_lean(CURRENT_SOURCE)
    data = inputs(machine)
    classification = []
    if args.odd_classification:
        for line in data.splitlines()[49:]:
            f = list(map(int, line.split()))
            if f[0] == 2 and (f[1] % 2 or f[1] == 2):
                classification.append(' '.join(map(str, [4]+f[1:])))
    if args.pairs_only or args.whole_phase_only:
        lines = data.splitlines()
        fixtures = [line for line in lines[49:] if
                    not line.startswith('2 ') and (not args.whole_phase_only or not line.startswith('3 '))]
        core = sum(line.startswith('3 ') for line in fixtures)
        data = '\n'.join(lines[:48]+[f'{core} {len(fixtures)}']+fixtures)+'\n'
    if args.outer_through:
        lines = data.splitlines()
        fixtures = [line for line in lines[49:] if not line.startswith('1 ')]
        core = len(fixtures)
        fixtures += [' '.join(map(str, outer_fixture(machine, n)))
                     for n in range(4, args.outer_through+1) if not args.even_only or n % 2 == 0]
        data = '\n'.join(lines[:48]+[f'{core} {len(fixtures)}']+fixtures)+'\n'
    if args.even_only:
        lines = data.splitlines()
        fixtures = [line for line in lines[49:] if not line.startswith('1 ') or int(line.split()[1]) % 2 == 0]
        core = sum(not line.startswith('1 ') for line in fixtures)
        data = '\n'.join(lines[:48]+[f'{core} {len(fixtures)}']+fixtures)+'\n'
    if classification:
        lines = data.splitlines()
        fixtures = classification+lines[49:]
        data = '\n'.join(lines[:48]+[f'{len(classification)} {len(fixtures)}']+fixtures)+'\n'
    sources = ('search23.cpp', 'phase_screen.hpp', 'search23.py', 'search_scans.py')
    metadata = {'method': args.method, 'groups': args.groups, 'repairs': args.repairs,
                'merge_pairs': args.merge_pair,
                'fixed_edges': args.fixed_edge,
                'editable_states': sorted(args.editable_states) if args.editable_states is not None else None,
                'pairs_only': args.pairs_only, 'whole_phase_only': args.whole_phase_only,
                'phase_factor': args.phase_factor,
                'outer_through': args.outer_through,
                'even_only': args.even_only, 'max_survivors': args.max_survivors,
                'odd_classification': args.odd_classification,
                'classification_offset': args.classification_offset,
                'success_certificates': args.success_certificates,
                'survivors_per_pair': args.survivors_per_pair,
                'input_sha256': hashlib.sha256(data.encode()).hexdigest(),
                'source_sha256': {name: hashlib.sha256((ROOT/'tools'/name).read_bytes()).hexdigest()
                                  for name in sources},
                'bootstrap': {'steps': args.bootstrap_steps, 'max_even': args.bootstrap_max_even,
                              'tape_cells': args.bootstrap_tape, 'max_ones': args.bootstrap_max_ones},
                'scope': 'Bounded fixtures and fixed phase interfaces; no lower bound or correctness proof. Later bootstrap boundaries require proof of skipped even cases.'}
    (args.output/'run.json').write_text(json.dumps(metadata, indent=2)+'\n')
    (args.output/'input.txt').write_text(data)
    with tempfile.TemporaryDirectory(prefix='goldbach23-') as directory:
        output = Path(directory)/('screen.dylib' if sys.platform == 'darwin' else 'screen.so')
        flags = ['-DSCREEN_LIBRARY', '-shared', '-fPIC'] if args.method == 'solver' else []
        flags += [f'-DPHASE_FACTOR={args.phase_factor}',
                  f'-DCLASSIFICATION_OFFSET={args.classification_offset}',
                  f'-DSUCCESS_CERTIFICATES={int(args.success_certificates)}',
                  f'-DBOOTSTRAP_STEPS={args.bootstrap_steps}',
                  f'-DBOOTSTRAP_MAX_EVEN={args.bootstrap_max_even}',
                  f'-DBOOTSTRAP_TAPE={args.bootstrap_tape}',
                  f'-DBOOTSTRAP_MAX_ONES={args.bootstrap_max_ones}']
        subprocess.run([compiler, '-std=c++17', '-O3', *flags, str(ROOT/'tools/search23.cpp'),
                        '-o', str(output)], check=True)
        if args.method == 'solver':
            solver_search(args, output, data)
        else:
            subprocess.run([str(output), str(args.output.resolve()), str(args.repairs), args.groups],
                           input=data, text=True, check=True)


if __name__ == '__main__':
    main()
