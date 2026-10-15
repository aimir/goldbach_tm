# Searching below 24 states

The accepted result is still the [24-state machine](REDUCTION.md), with its
[default-build Lean theorem](../formal/GoldbachTm.lean). No 23-state replacement
has passed this search's checks. This is not evidence that 24 is minimal.

## Completed native search

The one-repair run checked 847,044 tables after trace pruning. The two-repair
run performed **1,243,956,932 evaluations**, covering all 552 ordered state pairs
under the contracts below. Both returned zero finite survivors. Counts include
repeated tables reached through different repair orders; they are not counts of
distinct Turing machines.

The four-repair solver run checked 420,000 tables. Two six-repair runs checked
126,000 tables each, one retaining the primality interface and one allowing it
to change. None produced a finite survivor. Every state-pair run reached its
candidate budget: these runs establish no UNSAT result for four or six repairs.

The broader initialization run also completed all 552 pairs with one and two
repairs, under one million startup steps, 32,768 cells, 2,048 ones and a permitted
first even boundary anywhere from 4 through 256. It found zero finite survivors.
In the one-repair run, all 847,044 candidates failed the arithmetic contracts;
none even reached the initialization screen. Startup bounds therefore were not
the obstruction in that family.

A whole-phase search allowed eight repaired branches and changed primality/pair
interfaces, using every outer input 4–64 and twelve times the baseline arithmetic
time. All 42 pairs exhausted their 3,000-candidate budgets: 126,000 checks and no
survivor. A further structural run tried deleting 14 into 13, 5 into 7, and 8 into
7. Each could freely replace all 36 branches in the marker/primality fragment and
its compensating callers; only states 1, 2, 3, 21 and 23 stayed fixed. All three
exhausted 10,000-candidate budgets, with no survivor. None reached initialization;
their longest successful fixture prefix ended before the no-pair input 11.
These budget-limited searches establish no impossibility result.

## Search model

Choose an ordered pair of states, redirect every incoming transition from the
removed state to the retained state, then repair a bounded number of surviving
transitions. A repair may change the write bit, direction and target together,
or introduce a halting transition. It cannot reintroduce the removed state.
Try every surviving state as the initial state on an all-zero tape.

The scan groups in the current table are `(13,14,16,18,20,22)`, `(11,19,21)` and
`(5,7,8)`: 42 ordered pairs. `--groups all` expands this to all 552 ordered pairs.
Candidate JSON retains the original 24 row labels and identifies the omitted
row explicitly. Those files are proposals, not a published 23-state machine.
An accepted replacement would need a compact literal table and an unbounded proof.

The native repair search uses a failing execution trace to select the next
transition to change. A candidate agreeing on every branch in that trace repeats
the failure. Thus it can skip repairs to branches outside the trace. Bootstrap
failure uses the union of traces from every permitted initial state.

The optional Z3 mode uses the same observation as a learned constraint. Each
transition is a finite-domain variable, with a cardinality bound on changes from
the merged table. After a failed run it adds a clause requiring at least one
visited branch to change. It does not encode or assume Goldbach's conjecture.
Each solver call has a two-second timeout and a 768 MB memory setting. Each
ordered pair also has an explicit candidate budget. `budget` and `unknown` are
inconclusive; `unsat` concerns only the encoded finite search problem.

## Contracts and limits

The default 51 fixtures cover positive primality inputs, successful and failed
prime pairs, even outer-loop inputs, and synthetic odd inputs with no prime-pair
decomposition. Python's independent arithmetic oracle supplies the expected
outcomes. The shared C++ checker requires:

- The first primality return at the designated exit location has the right exit
  state and exactly restores the input tape. An incorrect return is rejected even
  if a later return would look correct.
- The first canonical pair boundary advances the failed split by one, or the
  first canonical outer boundary has exactly two additional ones after success.
  A boundary with the wrong number of ones is rejected immediately.
- A whole-number phase returns its next boundary on a positive fixture and halts
  on a negative fixture.
- Some initial state reaches the canonical boundary for 4 from blank tape.

`--pairs-only` drops the standalone primality contract, allowing changes to the
internal primality interface while retaining pair/outer behavior. It still fixes
the boundary tape representation. A valid machine with a different representation,
phase structure or startup at a later verified even number could be missed.

`--whole-phase-only` also drops the pair-return contracts. It permits a primality
fragment to leave a changed tape for the pair-advance caller, and permits their
fusion, provided the complete outer phase retains its arithmetic behavior.
`--outer-through 64` supplies all 61 outer inputs from 4 through 64, including
odd inputs with a prime pair as well as odd inputs without one. This prevents
the weaker screen from accepting a simple even/odd discriminator on that range.
The outer boundary representation remains fixed, so this is still a restricted
search family. `--phase-factor` increases its per-fixture time allowance.

The blank initialization screen now has independent configurable bounds. It can
run through intermediate phases and accept any canonical even outer boundary
from 4 through `--bootstrap-max-even`, from any surviving initial state. A later
boundary is only a proposal: preserving the exact headline theorem also requires
Lean proofs of every skipped even instance, plus exact blank initialization and
unbounded eventual progress through the caller-compatible arithmetic phases.
For example, starting at 10 requires proofs for 4, 6 and 8.

Solver options `--merge-pair DEAD KEEP` and `--editable-states 4,5,6,7,8,9` can
select a structural fragment and its compensating caller rows. Setting a repair
allowance at least as large as the number of editable branches allows their
complete resynthesis; the other rows retain the redirected quotient table.

Runs use 1,024 tape cells, keep the head within indices 128–895, permit at most
12 more ones than the fixture starts with, and allow `3 * baseline_steps + 100`
transitions per fixture. The bootstrap budget is 235 transitions. These are search
bounds, not assumptions of the Lean theorem. No finite fixture suite establishes
unbounded correctness, and failure is not a lower bound on equivalent machines.
These remain the defaults; the broader runs below explicitly replace them.

## Reproduce

Python 3.10 or newer and a C++17 compiler suffice for the native search:

```sh
python3 tools/search23.py --groups all --output scratch/search23-one
python3 tools/search23.py --groups all --repairs 2 --output scratch/search23-two
```

The second command can take substantially longer. For the optional solver mode,
install the `z3-solver` Python package in your preferred environment, then run:

```sh
python3 tools/search23.py --method solver --repairs 4 --iterations 10000 --output scratch/search23-solver
python3 tools/search23.py --method solver --repairs 6 --iterations 3000 --seed 626 --output scratch/search23-solver6
python3 tools/search23.py --method solver --repairs 6 --iterations 3000 --seed 735 --pairs-only --output scratch/search23-pairs
```

Broaden initialization to one million steps, 32,768 tape cells and up to 2,048
ones, accepting a canonical boundary for any even number through 256:

```sh
python3 tools/search23.py --groups all --repairs 1 --bootstrap-steps 1000000 --bootstrap-max-even 256 --bootstrap-tape 32768 --bootstrap-max-ones 2048 --output scratch/search23-broad-one
```

Allow changed internal primality/pair conventions and eight repaired branches,
with twelve times the baseline arithmetic time and the broader initialization:

```sh
python3 tools/search23.py --method solver --repairs 8 --iterations 3000 --seed 1015 --whole-phase-only --outer-through 64 --phase-factor 12 --bootstrap-steps 1000000 --bootstrap-max-even 256 --bootstrap-tape 32768 --bootstrap-max-ones 2048 --output scratch/search23-fused-eight
```

Output directories must be empty. Each run records input/source hashes, settings
and a compact summary. Executables and shared libraries are compiled in temporary
storage and removed. Raw outputs go under ignored `scratch/`; they are not committed.
[optimization23.json](../reference/optimization23.json) contains the saved outcomes
and their exact scope.

Broader exploratory runs also tried alternative growth entries, combinations of
transition rewrites that passed the finite screens, direct quotients of those
tables, and stochastic repair. None produced an accepted smaller machine. Those
frontiers are not part of the reproducible result or the formal proof.

## Screening regression checks

[The native screen tests](../tests/test_search_screen.py) include a literal machine
that returns a damaged tape and later repairs it, and another that increments by
one twice instead of by two once. Both must be rejected at their first incorrect
return. Other tests reject a wrong pair size and deletion of the halting branch.

The strengthened screen still reproduces all seven finite 25-to-24 candidates,
including the selected candidate with its full Lean proof. The independent
24-state verification and original baseline-audit reports are unchanged. All
machine/proof files match the hashes in [proof24.json](../reference/proof24.json).
