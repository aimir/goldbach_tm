# A formally verified 24-state Goldbach Turing machine

**24 working states, two symbols, one tape; formally verified in Lean.** Starting
on an all-zero tape, this machine halts if and only if Goldbach's conjecture is
false. This improves the [25-state construction by Yijun Leng](https://github.com/lengyijun/goldbach_tm)
by one state (4%).

The [headline theorem](formal/GoldbachTm.lean), checked by the default Lean build,
is:

```lean
(∃ i, Tm24.nth_cfg i = none) ↔
  (∃ n : ℕ, ¬ ∃ p q : ℕ, p + q = 2*n+4 ∧ Nat.Prime p ∧ Nat.Prime q)
```

The [literal transition table](machines/goldbach24.tm) starts in **state 18**.
The starting state is one of the 24 working states; there are no extra startup
states, prewritten input, or arithmetic oracles. The Lean working-state type is
literally `Fin 24`. Halting is a separate outcome, not a working state.

## The reduction

Only one original transition changes: state 0 reading 0 now writes 0, moves right,
and enters state 10. This reuses the arithmetic marker-transfer loop to join two
unary blocks and add two ones. Original state 22 becomes unreachable and is
removed. Starting in state 18 reaches the usual boundary for 4 in 25 steps.

[The construction and proof](docs/REDUCTION.md) explain the invariant and state
renumbering. The new proof adapts the upstream primality and pair-search lemmas;
the superseded full 25-state proof is not duplicated here. Its original transition
source remains as a baseline audit fixture. See [provenance](reference/upstream.json)
and the upstream [Apache-2.0 license](LICENSE).

## Results

| Check | Result |
| --- | --- |
| Working states | **25 → 24** |
| Default Lean build | Passed, including the headline equivalence |
| Headline axiom dependencies | `propext`, `Classical.choice`, `Quot.sound` |
| Reproducible scan-sharing search | 218,976 candidates; seven finite survivors |
| Selected candidate | Full unbounded Lean proof |
| Primality checks | 256 cases, with exact tape restoration |
| Growth checks | 1,056 block pairs, including an empty right block |
| First pair-search boundary checks | 199 cases |
| Whole-number phase checks | 63 even inputs; 13 synthetic odd no-pair inputs |
| Blank-tape simulation | 1,000,000 steps |
| 23-state local repair search | 552 ordered pairs; up to two repairs; no finite survivors |
| Regression tests | 29 passed |

The current verified result remains 24 states. The [23-state search](docs/SEARCH.md)
adds trace-guided transition repair and an optional constraint solver; no smaller
machine has been accepted. Broader startup through even 256, changed internal
primality/pair conventions, and complete fragment resynthesis have also produced
no accepted replacement; the saved results describe each bounded search's scope.

Synthetic odd inputs exercise the halting path; they are not Goldbach
counterexamples on the blank-tape run. Finite tests screen candidates. The Lean
theorem establishes correctness for all inputs reached from the blank tape.

## Verify and reproduce

With elan installed:

```sh
cd formal
lake build
lake env lean CheckAxioms.lean
```

The project pins Lean and mathlib. The first build needs their dependencies;
[the formal guide](formal/README.md) includes the optional targeted cache command.

From the repository root, using Python 3.10 or newer:

```sh
python3 tools/verify24.py
python3 -m unittest discover -s tests -v
python3 tools/audit.py
```

To replay the search, also install a C++17 compiler:

```sh
python3 tools/search_scans.py --output scratch/scan-sharing
```

The output directory must be empty. The search uses one process and bounded tape
fixtures; it does not prove its other survivors correct.

## Layout

- [`formal/`](formal/README.md): the current 24-state proof and headline theorem.
- [`machines/`](machines/README.md): current and baseline transition tables.
- [`tools/`](tools/README.md): verification, baseline audits and search replay.
- [`tests/`](tests/README.md): regression tests and deliberate corruption checks.
- [`reference/`](reference/README.md): provenance and compact verification evidence.
- [`docs/`](docs/README.md): construction and baseline analysis.

No logs, binaries, dependency caches, historical PDF, or raw search frontiers are
tracked in Git.

## Release and citation

The [v0.1.0 release](https://github.com/aimir/goldbach_tm/releases/tag/v0.1.0)
collects the 24-state table, Lean proof, reproduction tools and curated search
results. [CI](https://github.com/aimir/goldbach_tm/actions/workflows/verify.yml)
rebuilds the proof, checks the headline axiom dependencies and runs the
computational checks. [CITATION.cff](CITATION.cff) provides release metadata;
please also credit the upstream construction and proof described above.

The published branch preserves the upstream Git history. Historical upstream
artifacts remain in that history; the current tree contains only source and text
artifacts.
