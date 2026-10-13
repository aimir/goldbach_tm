"""Literal binary TM semantics and strict extraction from the upstream Lean table.

A missing transition halts immediately, matching Lean's `none`. It does not
perform a final write or move. State counts exclude that halting outcome.
"""
from dataclasses import dataclass
from pathlib import Path
import re
from math import isqrt

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / 'reference/upstream/TuringMachine25.lean'
Edge = tuple[int, int, int]  # write, move (+1 right), target
Machine = tuple[tuple[Edge | None, Edge | None], ...]


def load_lean(path: Path = SOURCE) -> Machine:
    text = path.read_text()
    size = int(re.search(r'def Machine := Fin (\d+) → Γ', text).group(1))
    body = text.split('def machine : Machine\n', 1)[1].split('\ndef nth_cfg', 1)[0]
    rows = {}
    edge = re.compile(r'\| ⟨\s*(\d+), _⟩, Γ\.(zero|one)\s*=> some ⟨⟨\s*(\d+), by omega⟩, ⟨Turing.Dir\.(left|right), Γ\.(zero|one)⟩⟩')
    halt = re.compile(r'\| ⟨\s*(\d+), _⟩, Γ\.(zero|one)\s*=> none')
    for line in body.splitlines():
        line = line.strip()
        if not line:
            continue
        if match := edge.fullmatch(line):
            q, b, target, move, write = match.groups()
            key = int(q), int(b == 'one')
            value = int(write == 'one'), 1 if move == 'right' else -1, int(target)
        elif match := halt.fullmatch(line):
            q, b = match.groups()
            key, value = (int(q), int(b == 'one')), None
        elif line.startswith(f'| ⟨_+{size}, _⟩, _ => by omega'):
            continue
        else:
            raise ValueError(f'Unrecognized machine definition: {line}')
        if key in rows:
            raise ValueError(f'Duplicate transition: {key}')
        rows[key] = value
    if set(rows) != {(q, b) for q in range(size) for b in range(2)}:
        raise ValueError(f'Expected exactly {size} states, each with two branches')
    result = tuple(tuple(rows[q, b] for b in range(2)) for q in range(size))
    if any(e is not None and not 0 <= e[2] < size for row in result for e in row):
        raise ValueError('Invalid target')
    return result


def format_machine(machine: Machine, start: int = 0) -> str:
    assert 0 <= start < len(machine)
    def fmt(edge):
        if edge is None:
            return 'HALT'
        w, d, q = edge
        return f'{w}{"R" if d == 1 else "L"}{q}'
    header = f'# start: {start}\n' if start else ''
    return header + ''.join(f'{q}: {fmt(row[0])} {fmt(row[1])}\n' for q, row in enumerate(machine))


@dataclass
class Config:
    state: int | None
    head: int
    ones: set[int]

    def advance(self, machine: Machine) -> None:
        if self.state is None:
            return
        edge = machine[self.state][int(self.head in self.ones)]
        if edge is None:
            self.state = None
            return
        write, direction, self.state = edge
        if write:
            self.ones.add(self.head)
        else:
            self.ones.discard(self.head)
        self.head += direction


def prime(n: int) -> bool:
    return n >= 2 and all(n % d for d in range(2, isqrt(n) + 1))


def goldbach(n: int) -> bool:
    return any(prime(p) and prime(n-p) for p in range(2, n-1))


def check_prime(machine: Machine, n: int, left=(), right=(), limit=2_000_000) -> int:
    """Check upstream prime_20/n_prime_16 interfaces, including untouched context."""
    ones = set(range(n))
    ones.update(-2-i for i, b in enumerate(left) if b)
    ones.update(n+1+i for i, b in enumerate(right) if b)
    cfg = Config(0, 0, ones.copy())
    for steps in range(1, limit+1):
        cfg.advance(machine)
        if cfg.head == -1 and cfg.state in (16, 20):
            expected = 20 if prime(n) else 16
            assert cfg.state == expected, ('primality result', n, cfg.state, expected)
            assert cfg.ones == ones, ('primality tape restoration', n)
            return steps
        assert cfg.state is not None, ('unexpected halt in primality', n)
    raise AssertionError(('primality step limit', n, limit))


def check_outer(machine: Machine, n: int, limit=5_000_000) -> dict:
    """Even positive cases; odd no-pair inputs exercise the halting path.

Odd no-pair inputs are synthetic phase fixtures, not reachable blank-tape
Goldbach counterexamples. The upstream no-pair lemma does not require parity.
"""
    represents = goldbach(n)
    assert n >= 4 and (n % 2 == 0 or not represents)
    cfg = Config(21, n, set(range(n)))
    for steps in range(1, limit+1):
        cfg.advance(machine)
        if cfg.state is None:
            assert not represents, ('unexpected outer halt', n)
            return {'input': n, 'outcome': 'halt', 'steps': steps}
        if cfg.state == 21 and cfg.head not in cfg.ones and cfg.ones:
            expected = set(range(cfg.head-len(cfg.ones), cfg.head))
            if cfg.ones == expected:
                assert len(cfg.ones) == n+2, ('wrong first outer boundary', n, len(cfg.ones))
                assert represents, ('unexpected outer success', n)
                return {'input': n, 'outcome': 'next_even', 'steps': steps}
    raise AssertionError(('outer step limit', n, limit))
