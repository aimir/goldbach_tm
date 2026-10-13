"""Independent finite checks of the literal 24-state construction.

The unbounded theorem is proved separately by the default Lean build.
"""
import argparse
import hashlib
import json
from pathlib import Path

from machine import ROOT, Config, load_lean, format_machine, check_prime, check_outer, goldbach, prime

CURRENT_SOURCE = ROOT/'formal/GoldbachTm/Tm24/Machine.lean'


def construction():
    original = load_lean()
    current = load_lean(CURRENT_SOURCE)
    def renumber(q):
        assert q != 22
        return q if q < 22 else q-1
    expected = []
    for q, row in enumerate(original):
        if q == 22:
            continue
        expected.append(tuple(None if edge is None else
            (0, 1, 10) if (q, b) == (0, 0) else
            (edge[0], edge[1], renumber(edge[2])) for b, edge in enumerate(row)))
    assert current == tuple(expected)
    assert len(current) == 24
    assert '⟨⟨18, by omega⟩, Turing.Tape.mk₁ l⟩' in CURRENT_SOURCE.read_text()
    return current


def check_growth(machine, p, q):
    """Two blocks of lengths p>=1, q>=0, all other cells blank."""
    assert p >= 1 and q >= 0
    cfg = Config(0, 0, set(range(1, p+1)) | set(range(p+2, p+q+2)))
    steps = q*q + (2*p+8)*q + 3*p + 12
    for _ in range(steps):
        cfg.advance(machine)
        assert cfg.state is not None
    assert (cfg.state, cfg.head, cfg.ones) == (21, p+q+2, set(range(p+q+2)))
    return steps


def check_pair(machine, p, q, limit=2_000_000):
    """Check the first canonical pair/outer boundary, rejecting a wrong early exit."""
    assert p >= 1 and q >= 1 and (p+q) % 2 == 0 and p+q >= 4
    cfg = Config(17, 0, set(range(-p, q+1)))
    both = prime(p) and prime(q)
    for steps in range(1, limit+1):
        cfg.advance(machine)
        assert cfg.state is not None, (p, q, 'halt')
        if cfg.state == 17 and cfg.head in cfg.ones:
            lo = min(cfg.ones)
            if cfg.ones == set(range(lo, lo+len(cfg.ones))):
                assert not both and len(cfg.ones) == p+q+1 and cfg.head-lo == p-1, (p, q, 'wrong next pair')
                return steps
        if cfg.state == 21 and cfg.ones and cfg.ones == set(range(cfg.head-len(cfg.ones), cfg.head)):
            assert len(cfg.ones) == p+q+2, (p, q, 'wrong first outer boundary')
            assert both, (p, q, 'accepted composite pair')
            return steps
    raise AssertionError((p, q, 'pair step budget'))


def bootstrap(machine):
    cfg = Config(18, 0, set())
    for _ in range(25):
        cfg.advance(machine)
    assert (cfg.state, cfg.head, cfg.ones) == (21, 3, {-1, 0, 1, 2})


def verify():
    machine = construction()
    assert (ROOT/'machines/goldbach24.tm').read_text() == format_machine(machine, start=18)
    bootstrap(machine)
    prime_steps = sum(check_prime(machine, n, left, right)
        for n in range(1, 129)
        for left, right in (((), ()), ((1, 0, 1, 1), (1, 1, 0, 1))))
    growth_steps = sum(check_growth(machine, p, q) for p in range(1, 33) for q in range(33))
    pairs = [(p, q) for p in range(1, 21) for q in range(1, 21)
             if (p+q) % 2 == 0 and p+q >= 4]
    pair_steps = sum(check_pair(machine, p, q) for p, q in pairs)
    evens = [check_outer(machine, n) for n in range(4, 130, 2)]
    odds = [check_outer(machine, n) for n in range(5, 65, 2) if not goldbach(n)]
    cfg = Config(18, 0, set())
    masks = [0]*24
    for _ in range(1_000_000):
        assert cfg.state is not None
        masks[cfg.state] |= 1 << int(cfg.head in cfg.ones)
        cfg.advance(machine)
    return {'states': 24, 'start_state': 18,
            'table_sha256': hashlib.sha256(format_machine(machine, start=18).encode()).hexdigest(),
            'bootstrap_steps': 25, 'bootstrap_even': 4,
            'primality': {'cases': 256, 'range': [1, 128], 'steps': prime_steps},
            'growth': {'cases': 1056, 'left_range': [1, 32], 'right_range': [0, 32], 'steps': growth_steps},
            'pair_boundaries': {'cases': len(pairs), 'summand_range': [1, 20], 'steps': pair_steps},
            'even_boundaries': evens, 'synthetic_halting_odd_boundaries': odds,
            'blank_trace_steps': 1_000_000, 'observed_read_masks': masks,
            'scope': 'Finite computational checks; unbounded correctness is a separate Lean theorem.'}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = verify()
    if args.output:
        args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({k: result[k] for k in ('states', 'start_state', 'bootstrap_steps', 'primality', 'growth', 'pair_boundaries')}))
    print('Outer cases:', len(result['even_boundaries']), 'even;', len(result['synthetic_halting_odd_boundaries']), 'synthetic halting')
