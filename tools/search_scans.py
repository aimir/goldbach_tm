"""Replay scan sharing, one-edge repair and free choice of initial state.

Only finite tests are used here. Survivors require independent validation and
an unbounded argument. The selected 24-state machine has a separate Lean proof.
"""
import argparse
from pathlib import Path
import shutil
import subprocess
import tempfile

from machine import ROOT, load_lean, check_prime, check_outer, prime
from verify24 import check_pair


def inputs(machine=None):
    machine = load_lean() if machine is None else machine
    core = [(2, n, 0, prime(n), check_prime(machine, n)) for n in
            (1, 2, 3, 4, 5, 9, 7, 6, 11, 15, 13)]
    for p, q in [(2,2),(4,4),(3,3),(5,3),(3,5),(4,2),(2,4),(6,6),
                 (9,3),(3,9),(9,9),(1,3),(7,5),(5,7),(7,7),(11,9),(9,11)]:
        core.append((3, q, p, prime(p) and prime(q), check_pair(machine, p, q)))
    outer = []
    for n in (4,6,11,8,10,12,17,14,16,18,20,23,22,24,26,28,30,32,27,34,36,38,40):
        result = check_outer(machine, n)
        outer.append((1, n, 0, result['outcome'] != 'halt', result['steps']))
    lines = [' '.join(map(str, edge or (0,0,-1))) for row in machine for edge in row]
    lines.append(f'{len(core)} {len(core)+len(outer)}')
    lines.extend(' '.join(str(int(v)) for v in f) for f in core+outer)
    return '\n'.join(lines)+'\n'


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=ROOT/'scratch/scan-sharing')
    args = parser.parse_args()
    compiler = shutil.which('clang++') or shutil.which('g++')
    if compiler is None:
        parser.error('A C++17 compiler (clang++ or g++) is required')
    args.output.mkdir(parents=True, exist_ok=True)
    if any(args.output.iterdir()):
        parser.error('Output directory must be empty to avoid mixing runs')
    data = inputs()
    with tempfile.TemporaryDirectory(prefix='goldbach-scan-') as d:
        executable = Path(d)/'search_scans'
        subprocess.run([compiler, '-std=c++17', '-O3', str(ROOT/'tools/search_scans.cpp'),
                        '-o', str(executable)], check=True)
        subprocess.run([str(executable), str(args.output.resolve())], input=data,
                       text=True, check=True)
