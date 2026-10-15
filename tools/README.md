# Verification and search tools

- `verify24.py`: extracts the current Lean table, checks the one-edge construction
  and 24-state count, and tests initialization, primality, growth, pair boundaries,
  outer boundaries, synthetic halting cases and a million blank-tape steps.
- `machine.py`: strict Lean-table extraction, literal tape interpreter, independent
  integer primality/Goldbach oracles and baseline-compatible phase checks.
- `audit.py`: the 25-state baseline's observed branch witnesses, separately checked
  quotient-conflict certificate, finite-window abstraction and exact short-path
  enumeration. It does not optimize or formally prove the new machine.
- `search_scans.py` / `search_scans.cpp`: deterministic scan merging plus one edge
  repair, testing arithmetic interfaces and every surviving choice of initial
  state. The C++ executable is built in temporary storage and discarded.

- `search23.py` / `search23.cpp`: merge states of the current machine and repair
  one or two transitions, pruning with failing execution traces. Optional Z3 mode
  searches larger repair sets, permits whole-fragment synthesis with changed
  internal primality/pair conventions, and records budgets, UNSAT and UNKNOWN
  separately. Initialization can reach a later even boundary under independently
  enlarged tape/step bounds. Such a candidate still needs an unbounded Lean proof
  and proofs of all skipped even instances.
- `phase_screen.hpp`: shared native interpreter and first-boundary checks used by
  both search programs. It is tested against explicit corruptions and the Python
  interpreter.

Run from the repository root:

```sh
python3 tools/verify24.py
python3 tools/audit.py
python3 tools/search_scans.py --output scratch/scan-sharing
python3 tools/search23.py --groups all --output scratch/search23
```

Python 3.10 or newer suffices for verification. Search also needs a C++17 compiler.
The search output directory must be empty. Search uses bounded tape fixtures and
step budgets described in [its manifest](../reference/scan-sharing.json); a budget
failure is inconclusive outside that screening family. Its seven finite survivors
are not seven proved machines: only the selected state-10 entry has a Lean proof.

The computational tools do not invoke Lean and are not part of its trusted proof
path. See [formal verification](../formal/README.md).

For larger searches, modes and exact limitations, see [SEARCH.md](../docs/SEARCH.md).
The optional solver mode needs the `z3-solver` Python package. Neither solver
status nor finite-screening success is a Lean theorem or a machine-size lower bound.
