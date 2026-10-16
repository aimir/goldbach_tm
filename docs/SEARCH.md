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
All 847,044 one-repair and 1,243,956,932 two-repair candidates failed the arithmetic
contracts; none reached the initialization screen. Startup bounds therefore were
not the obstruction in either family.

A whole-phase search allowed eight repaired branches and changed primality/pair
interfaces, using every outer input 4–64 and twelve times the baseline arithmetic
time. All 42 pairs exhausted their 3,000-candidate budgets: 126,000 checks and no
survivor. A further structural run tried deleting 14 into 13, 5 into 7, and 8 into
7. Each could freely replace all 36 branches in the marker/primality fragment and
its compensating callers; only states 1, 2, 3, 21 and 23 stayed fixed. All three
exhausted 10,000-candidate budgets, with no survivor. None reached initialization;
their longest successful fixture prefix ended before the no-pair input 11.
These budget-limited searches establish no impossibility result.

An even-domain run retained twelve finite proposals after 2,455 solver models.
Most advance the outer number in four or six transitions for every tested input,
without performing the required arithmetic search. Recovered frontiers first
rejected at odd input 11 also passed every even input 4–128, but their boundary
times were constant at 10, 14 or 104 steps on inputs 4, 128 and 256. These tables
were retained and reviewed rather than rejected solely for odd-input behavior;
none supplies an unbounded reduction proof. Adding optional odd/2 classification
tests with free return tape produced zero survivors in 60,000 models over the
three fragment deletions. Those runs were budget-limited.

A separate structural template shares states 3 and 12, whose write bits and
directions agree on both branches. Two setup rewrites reproduce the old state-10
configuration in eight rather than ten steps for every initial primality input
at least four. This initial identity is insufficient: trial-divisor initialization
also enters that fragment. A seven-rewrite prototype restoring tiny inputs and
blank startup first misclassifies 11, where an internal marker stops the reused
eraser early. Any accepted construction must repair and prove that entire loop.

A revised seven-rewrite fragment fixes that trial reinitialization by preserving
the left counter during a scan and erasing its first cell before resuming. It
passes 256 primality checks on inputs 1–128, including arbitrary tape context:
composites return with exact restoration; primes leave their first input cell
erased and return there in state 20. This is an unproved arithmetic fragment,
not a Goldbach machine. Fixing that fragment and freeing six caller branches
produced four whole-phase bypass proposals in 125 models. With canonical pair
compatibility required, 50,000 models found no survivor; the strongest prefix
first failed on the successful pair `(3,5)`. Caller compatibility, halting on
exhaustion, and an unbounded proof remain necessary.
A fusion-oriented run instead required observed successful prime tests summing
to the outer input, without canonical pair boundaries. Its 50,000-model budget
also found no survivor; its best prefix advanced 4 but failed on 6. This does not
rule out other callers or tape representations.

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

Odd outer inputs are unreachable in the blank-tape Goldbach run. Their behavior
is a useful diagnostic, but requiring it can exclude a correct specialization to
even inputs. `--whole-phase-only --even-only` screens the reachable outer domain
and saves proposed machines with separate primality, pair and odd-input diagnostic
results. `--save-frontier` also retains the longest successful fixture prefix per
state pair, including tables first rejected on an unreachable odd input. These
files are explicitly marked unproved. A machine that always adds two can pass
every tested even instance, so this mode supplies no arithmetic correctness claim.

`--odd-classification` adds optional result-only tests for odd primality inputs
and 2. Unlike the original primality interface, these allow the return tape to
change and the head to return farther left, so the caller may consume a modified
layout. The prime/nonprime flags remain mapped states 20/16. This guides synthesis
away from trivial always-advance proposals while retaining another restricted
interface family; it is not a requirement of the headline theorem.
`--classification-offset 0` permits a flag on the first input cell, for example
when a prime routine leaves precisely that cell erased for its caller to restore.
Combining `--pairs-only --even-only` retains the canonical pair contracts while
dropping unreachable odd outer inputs, providing a stricter caller-composition
gate for such a fragment.

`--success-certificates` is another optional whole-phase guide for that family:
before an outer success, it requires observed prime-classification calls whose
input values sum to the current outer input. It does not require canonical failed
pair returns, so it can screen proposed summand/advance fusions. The checker keeps
these observations and checks them arithmetically; they are search instrumentation,
not extra tape, states, or an oracle in the candidate machine. This finite guide
rejects simple arithmetic bypasses and still cannot establish unbounded correctness.

The blank initialization screen now has independent configurable bounds. It can
run through intermediate phases and accept any canonical even outer boundary
from 4 through `--bootstrap-max-even`, from any surviving initial state. A later
boundary is only a proposal: preserving the exact headline theorem also requires
Lean proofs of every skipped even instance, plus exact blank initialization and
unbounded eventual progress through the caller-compatible arithmetic phases.
For example, starting at 10 requires proofs for 4, 6 and 8.
The default-build [finite-prefix proof](../formal/GoldbachTm/FinitePrefix.lean)
now supplies all even cases 4–256 and an exact tail-counterexample equivalence,
including the specialization to startup at 10. It supplies the skipped arithmetic
cases, while a replacement would still need its actual blank execution and
unbounded arithmetic/progress proofs.

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

For even-domain proposals with changed return tape, retain four proposals per
pair and apply the optional odd/2 classification guide:

```sh
python3 tools/search23.py --method solver --repairs 12 --merge-pair 14 13 --merge-pair 8 7 --merge-pair 5 7 --iterations 20000 --seed 1018 --whole-phase-only --even-only --odd-classification --outer-through 128 --phase-factor 12 --save-frontier --max-survivors 12 --survivors-per-pair 4 --bootstrap-steps 1000000 --bootstrap-max-even 256 --bootstrap-tape 32768 --bootstrap-max-ones 2048 --output scratch/search23-even-classification
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

## Unbounded changed-return arithmetic contract

The seven-rewrite classifier above now has a kernel-checked unbounded proof in
[`ChangedReturn/Contract.lean`](../formal/GoldbachTm/ChangedReturn/Contract.lean),
imported by the default build. `ChangedReturn.classifies` covers every positive
unary input and arbitrary separated left/right tape contexts. It proves strict
progress and the exact two returns: a nonprime input is restored completely and
returns in state 16 on its left separator; a prime input returns in state 20 on
its first input cell, erasing exactly that cell. `ChangedReturn.terminates`
proves termination when both exits are connected to halting transitions.

The arithmetic proofs quantify arbitrary transitions at the unused caller
branches. In particular they do not assume the old prime-return interface,
blank initialization, or any bounded simulation. The changed failed-divisor
route restores the original modular invariant before increasing the trial
divisor. The prime tail has an additional restoration sweep through states
12 and 14 before it reaches the changed return.

This is a proved fragment, not an accepted 23-state machine. Its formal type
retains the original `Fin 24` labels so callers can be composed explicitly. A
complete reduction still requires a caller using at most 23 states, exact blank
initialization, and unbounded outer progress. The current headline remains the
original 24-state theorem.

The compatible caller in
[`ChangedReturn/Adapter/`](../formal/GoldbachTm/ChangedReturn/Adapter/Correctness.lean)
now has a complete unbounded composition proof. It restores a prime return with
`20/0: 1,L,3` followed by `3/0: 0,L,22`. `Adapter.cfg27` proves literal blank
initialization to the boundary for four after 27 steps.
`Adapter.halts_iff_goldbach_counterexample` proves the same full Goldbach halting
equivalence for this table, including pair search and strict outer progress.
The helper occupies the state removed from the arithmetic body, leaving 24
states overall. It is a checked basis for further fusion, not a smaller-machine
claim, and the published Tm24 headline and table remain unchanged.

The certificate guide now accepts classification returns at or left of
`--classification-offset`. This matters for the proved fragment: a prime returns
at offset zero, while the nonprime input one returns at offset minus one. The
proved 24-state adapter is a regression control for that asymmetric convention;
its whole-phase fixtures must pass with `--classification-offset 0` and
`--success-certificates` together. Direct arithmetic bypasses remain rejected.

A targeted helper-elimination family shares state 17: `20/0: 1,L,17` followed
by `17/0: 0,L,22`. The generic `ChangedReturn.restore_prime_exit` theorem proves
that these two transitions implement the required local return. All 35 arithmetic
branches remain fixed in the experiments; the other caller branches may change.
With corrected certificates and even outer fixtures 4–128, 10,000 models for the
direct helper and 20,000 models with state 17's zero branch free produced no
survivor. A further 20,000 models restricted the direct helper to at most two
additional caller repairs. Its best frontier passed 4 and failed 6; separate
pair diagnostics also rejected composite-pair acceptance. These are exhausted
model budgets, not lower bounds. No model reached the initialization gate.
