"""Reproducible baseline audit; finite tests are not a Goldbach equivalence proof."""
from collections import deque
from itertools import combinations
from pathlib import Path
import argparse
import hashlib
import json

from machine import ROOT, SOURCE, Config, check_outer, check_prime, format_machine, goldbach, load_lean


def observe(machine, steps):
    cfg = Config(0, 0, set())
    masks = [0] * len(machine)
    first = {}
    for i in range(steps):
        if cfg.state is None:
            break
        bit = int(cfg.head in cfg.ones)
        masks[cfg.state] |= 1 << bit
        first.setdefault(f'{cfg.state}:{bit}', i)
        cfg.advance(machine)
    return masks, first


def conflicts(machine, masks):
    """Necessary conflicts for any state-only, step-preserving quotient.

Premises are witnessed reachable branches. A conflict either has differing
write/move/halting actions, or leads to an already-conflicting successor pair.
The certificate is ordered so each dependency precedes its user.
"""
    result = {}
    changed = True
    while changed:
        changed = False
        for a, b in combinations(range(len(machine)), 2):
            if (a, b) in result:
                continue
            for bit in (0, 1):
                if not (masks[a] & masks[b] & (1 << bit)):
                    continue
                x, y = machine[a][bit], machine[b][bit]
                reason = None
                if (x is None) != (y is None) or (x is not None and y is not None and x[:2] != y[:2]):
                    reason = {'kind': 'action', 'read': bit}
                elif x is not None and y is not None:
                    dep = tuple(sorted((x[2], y[2])))
                    if dep in result:
                        reason = {'kind': 'successor', 'read': bit, 'pair_dependency': list(dep)}
                if reason is not None:
                    result[a, b] = reason
                    changed = True
                    break
    return [{'pair': list(pair), **reason} for pair, reason in result.items()]


def check_certificate(machine, first, certificate):
    """Replay every reachability witness, then independently check conflicts."""
    expected = {tuple(map(int, key.split(':'))): step for key, step in first.items()}
    cfg = Config(0, 0, set())
    witnessed = set()
    for i in range(max(expected.values(), default=-1) + 1):
        assert cfg.state is not None
        pair = cfg.state, int(cfg.head in cfg.ones)
        if expected.get(pair) == i:
            witnessed.add(pair)
        cfg.advance(machine)
    assert witnessed == set(expected)
    bad = set()
    for item in certificate:
        a, b = item['pair']
        bit = item['read']
        assert 0 <= a < b < len(machine) and (a, b) not in bad
        assert (a, bit) in witnessed and (b, bit) in witnessed
        x, y = machine[a][bit], machine[b][bit]
        if item['kind'] == 'action':
            assert (x is None) != (y is None) or (x is not None and y is not None and x[:2] != y[:2])
        else:
            assert item['kind'] == 'successor' and x is not None and y is not None
            dependency = tuple(sorted((x[2], y[2])))
            assert dependency == tuple(item['pair_dependency'])
            assert dependency in bad
        bad.add((a, b))
    return len(bad)


def tape_windows(machine, radius):
    """Sound overapproximation: each newly exposed boundary cell may be 0 or 1."""
    width = 2 * radius + 1
    full = (1 << width) - 1
    todo = deque([(0, 0)])
    seen = {(0, 0)}
    possible = [0] * len(machine)
    while todo:
        state, window = todo.popleft()
        bit = (window >> radius) & 1
        possible[state] |= 1 << bit
        edge = machine[state][bit]
        if edge is None:
            continue
        write, direction, target = edge
        window = (window & ~(1 << radius)) | (write << radius)
        if direction == 1:
            base, extra = window >> 1, 1 << (width-1)
        else:
            base, extra = (window << 1) & full, 1
        for nxt in ((target, base), (target, base | extra)):
            if nxt not in seen:
                seen.add(nxt)
                todo.append(nxt)
    return {'radius': radius, 'configurations': len(seen), 'possible_read_masks': possible}


def collapse(machine, state, bit, length):
    """Exhaust all initially unknown cells for an exact length-to-one rewrite.

Successful paths must have identical target/write/move, finish one cell away,
restore every other touched cell, and never halt early. No empirical tape
invariant is assumed, and no change in tape representation is allowed.
"""
    paths = [(state, 0, {0: bit}, {})]
    for step in range(length):
        successors = []
        for state, head, initial, written in paths:
            values = [written[head]] if head in written else ([initial[head]] if head in initial else [0, 1])
            for read in values:
                edge = machine[state][read]
                if edge is None:
                    return None
                write, direction, target = edge
                origin, changed = initial.copy(), written.copy()
                origin.setdefault(head, read)
                changed[head] = write
                new_head = head + direction
                if abs(new_head) > length-step:
                    return None
                successors.append((target, new_head, origin, changed))
        paths = successors
    outcomes = set()
    for state, head, initial, written in paths:
        if abs(head) != 1 or any(pos != 0 and value != initial[pos] for pos, value in written.items()):
            return None
        outcomes.add((written.get(0, bit), head, state))
    return next(iter(outcomes)) if len(outcomes) == 1 else None


def run():
    machine = load_lean()
    table = format_machine(machine)
    assert (ROOT / 'machines/goldbach25.tm').read_text() == table
    for name, digest in json.loads((ROOT/'reference/upstream.json').read_text())['unmodified_files_sha256'].items():
        assert hashlib.sha256((ROOT/name).read_bytes()).hexdigest() == digest, name
    masks, first = observe(machine, 1_000_000)
    cert = conflicts(machine, masks)
    assert check_certificate(machine, first, cert) == 300
    macros = []
    for length in range(3, 32, 2):
        hits = []
        for q in range(len(machine)):
            for bit in (0, 1):
                edge = collapse(machine, q, bit, length)
                if edge is not None and edge != machine[q][bit]:
                    hits.append({'state': q, 'read': bit, 'edge': edge})
        macros.append({'length': length, 'rewrites': hits})
    prime_steps = 0
    for n in range(1, 129):
        for left, right in (((), ()), ((1, 0, 1, 1), (1, 1, 0, 1))):
            prime_steps += check_prime(machine, n, left, right)
    outer = [check_outer(machine, n) for n in range(4, 66, 2)]
    negative = [check_outer(machine, n) for n in range(5, 65, 2) if not goldbach(n)]
    result = {
        'upstream_commit': json.loads((ROOT/'reference/upstream.json').read_text())['commit'],
        'table_sha256': hashlib.sha256(table.encode()).hexdigest(),
        'states': len(machine), 'halting_branches': sum(e is None for row in machine for e in row),
        'blank_steps': 1_000_000, 'observed_branches': len(first),
        'last_first_branch_step_zero_based': max(first.values()),
        'first_branch_visits': first, 'quotient_conflicts': cert,
        'incompatible_pairs': len(cert),
        'quotient_scope': 'State-only step-preserving quotients, same tape and head position; not a lower bound on equivalent TMs.',
        'tape_windows': [tape_windows(machine, r) for r in range(2, 7)],
        'all_input_macro_search': macros,
        'primality_tests': {'integers': [1, 128], 'contexts_per_integer': 2, 'cases': 256, 'steps': prime_steps},
        'even_outer_tests': outer, 'synthetic_no_pair_odd_tests': negative,
        'verification': 'Computational audit of the pinned 25-state table; independent of the current 24-state Lean proof.',
    }
    return result


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = run()
    if args.output:
        args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({key: result[key] for key in ('states', 'observed_branches', 'incompatible_pairs', 'primality_tests')}))
    print('Even phase cases:', len(result['even_outer_tests']), '; synthetic halting cases:', len(result['synthetic_no_pair_odd_tests']))
