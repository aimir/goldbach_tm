# Compatibility adapter (24 states)

This caller restores the changed prime exit and proves a complete blank-tape
machine. It uses the freed state 3 as a helper, so it still has 24 states.
It does not replace the original Tm24 headline or claim a smaller machine.

- `Machine.lean` defines the caller and exact all-zero start. Its two adapter
  transitions restore the first input cell, move left through state 3, and skip
  the separator into state 22. `cfg27` proves the startup to the boundary for 4.
- `Scans.lean` provides the caller's left/right unary scans.
- `Growth.lean` proves that joining two blocks adds two ones.
- `PairSearch.lean` proves failed-pair advancement, successful growth, and
  exhaustion when no prime pair exists, using the generic arithmetic contracts.
- `Correctness.lean` proves unbounded outer progress and
  `halts_iff_goldbach_counterexample` for `run caller start`.

The contracts preserve the exact canonical caller layouts used by Tm24; the
changed arithmetic return is repaired by an additional caller step. All proof
files are imported by the default build and checked by the ordinary Lean kernel.
