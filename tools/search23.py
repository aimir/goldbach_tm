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

from machine import ROOT, load_lean
from verify24 import CURRENT_SOURCE
from search_scans import inputs

SCAN_GROUPS = ((13,14,16,18,20,22), (11,19,21), (5,7,8))


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
    pairs = [(d,k) for group in groups for d in group for k in group if d != k]
    random.Random(args.seed).shuffle(pairs)
    report = {'method': 'counterexample_guided_solver', 'z3': z3.get_version_string(),
              'repairs': args.repairs, 'seed': args.seed, 'pairs': [], 'finite_survivors': 0}
    for dead, keep in pairs:
        old = [encode([w,d,keep if q == dead else q]) for w,d,q in baseline]
        solver = z3.Solver()
        solver.set(timeout=2000, max_memory=768, random_seed=args.seed)
        edges = [z3.Int(f'e{i}') for i in range(48)]
        active = [i for i in range(48) if i//2 != dead]
        for i in active:
            solver.add(edges[i] >= 0, edges[i] <= 96,
                       z3.Or(edges[i] < 1+4*dead, edges[i] >= 5+4*dead))
        for i in range(48):
            if i//2 == dead:
                solver.add(edges[i] == old[i])
        solver.add(z3.PbLe([(edges[i] != old[i], 1) for i in active], args.repairs))
        # A machine with no halting transition cannot pass the negative fixtures.
        solver.add(z3.Or([edges[i] == 0 for i in active]))
        result = {'removed': dead, 'merged_into': keep, 'checks': 0, 'status': 'budget'}
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
            if failed < 0:
                result['status'] = 'finite_survivor'
                report['finite_survivors'] += 1
                candidate = {'removed': dead, 'merged_into': keep, 'start': trace.value,
                             'table': [[decode(values[2*q]), decode(values[2*q+1])]
                                       for q in range(24)]}
                (args.output/f'candidate-{report["finite_survivors"]}.json').write_text(
                    json.dumps(candidate, indent=2)+'\n')
                break
            # Every table agreeing on these visited edges repeats this failure.
            # In the bootstrap case the trace covers every possible initial state.
            solver.add(z3.Or([edges[i] != values[i] for i in active if trace.value >> i & 1]))
        report['pairs'].append(result)
        (args.output/'summary.json').write_text(json.dumps(report, indent=2)+'\n')
        print(f'{dead} -> {keep}: {result["status"]}, {result["checks"]} checked tables', flush=True)
        if report['finite_survivors']:
            break


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=ROOT/'scratch/search23')
    parser.add_argument('--method', choices=('repair','solver'), default='repair')
    parser.add_argument('--repairs', type=int, help='Default: 1 for repair, 4 for solver')
    parser.add_argument('--groups', choices=('scans','all'), default='scans')
    parser.add_argument('--pairs-only', action='store_true', help='Allow changes to the internal primality interface')
    parser.add_argument('--iterations', type=int, default=10000, help='Solver candidate budget per ordered state pair')
    parser.add_argument('--seed', type=int, default=2423)
    args = parser.parse_args()
    args.repairs = args.repairs if args.repairs is not None else (1 if args.method == 'repair' else 4)
    if not 1 <= args.repairs <= (2 if args.method == 'repair' else 46) or args.iterations < 1:
        parser.error('Invalid repair count or solver candidate budget')
    compiler = shutil.which('clang++') or shutil.which('g++')
    if compiler is None:
        parser.error('A C++17 compiler is required')
    args.output.mkdir(parents=True, exist_ok=True)
    if any(args.output.iterdir()):
        parser.error('Output directory must be empty')
    data = inputs(load_lean(CURRENT_SOURCE))
    if args.pairs_only:
        lines = data.splitlines()
        fixtures = [line for line in lines[49:] if not line.startswith('2 ')]
        core = sum(line.startswith('3 ') for line in fixtures)
        data = '\n'.join(lines[:48]+[f'{core} {len(fixtures)}']+fixtures)+'\n'
    sources = ('search23.cpp', 'phase_screen.hpp', 'search23.py', 'search_scans.py')
    metadata = {'method': args.method, 'groups': args.groups, 'repairs': args.repairs,
                'pairs_only': args.pairs_only, 'input_sha256': hashlib.sha256(data.encode()).hexdigest(),
                'source_sha256': {name: hashlib.sha256((ROOT/'tools'/name).read_bytes()).hexdigest()
                                  for name in sources},
                'scope': 'Bounded fixtures, fixed phase interfaces, bootstrap at 4; no lower bound or correctness proof.'}
    (args.output/'run.json').write_text(json.dumps(metadata, indent=2)+'\n')
    (args.output/'input.txt').write_text(data)
    with tempfile.TemporaryDirectory(prefix='goldbach23-') as directory:
        output = Path(directory)/('screen.dylib' if sys.platform == 'darwin' else 'screen.so')
        flags = ['-DSCREEN_LIBRARY', '-shared', '-fPIC'] if args.method == 'solver' else []
        subprocess.run([compiler, '-std=c++17', '-O3', *flags, str(ROOT/'tools/search23.cpp'),
                        '-o', str(output)], check=True)
        if args.method == 'solver':
            solver_search(args, output, data)
        else:
            subprocess.run([str(output), str(args.output.resolve()), str(args.repairs), args.groups],
                           input=data, text=True, check=True)


if __name__ == '__main__':
    main()
