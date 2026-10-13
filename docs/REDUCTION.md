# The 24-state construction

## Literal changes

Using the original state labels:

1. Replace `0,0 → 1,R,22` with `0,0 → 0,R,10`.
2. Start in state 18 instead of state 0.
3. Delete original state 22, which then has no incoming edge from another state.

The published table renumbers original states 23 and 24 as 22 and 23;
original states 0–21 retain their labels. Its initial state is explicitly 18.
The formal table uses `Fin 24`, so the deleted state is absent from the machine,
not merely discounted in a reachability claim.

## Why the reused routine works

The new growth entry has state 0 on a blank cell, with all cells to its left blank
and, to its right, `1^p 0 1^q`, where `p ≥ 1` and `q ≥ 0`. The output is the usual
state-21 boundary just to the right of `1^(p+q+2)`, with everything else blank.

After the changed transition, state 10 is on the first one. When the second block
is nonempty, states 10–13, 6, 8 and 9 move its separator one cell right and return
to state 10. This changes the block lengths from `(p,q)` to `(p+1,q−1)` without
changing their sum. The proof reuses the primality routine's marker-transfer
lemma at modulus one; its remaining left counter must stay zero.

Once the second block is empty, states 10–12 and 14–16 fill the two remaining
holes. The result has `p+q+2` ones. The existing return path through states 17, 9
and 21 reaches the canonical outer boundary. The finite verifier also checks the
exact execution length `q² + (2p+8)q + 3p + 12` for this routine. The Lean proof
establishes existence of a later correct boundary without needing that formula.

The growth lemma requires no primality or parity assumption. In the Goldbach
program it is used after both summands have been proved prime. All primality
code and unsuccessful-pair behavior are unchanged apart from state renumbering.

On a blank tape, state 18 and the existing states 19, 2, 20 and 22 create a
two-one block and reach the growth entry. Growth then produces four ones. This
reaches the original outer-loop invariant after exactly 25 steps, so changing the
initial state needs no additional working states and skips no even input.

## Formal argument

[The default-build theorem](../formal/GoldbachTm.lean) states the full halting
iff-counterexample equivalence using `Nat.Prime` explicitly. The proof is for the
actual 24-state table and its blank-tape initialization.

- [Machine](../formal/GoldbachTm/Tm24/Machine.lean) defines the table and proves
  the 25-step bootstrap.
- [Primality](../formal/GoldbachTm/Tm24/Primality.lean) retains the upstream prime
  and composite exits, preserving the surrounding tape.
- [Growth](../formal/GoldbachTm/Tm24/Growth.lean) proves the replacement for
  arbitrary block lengths.
- [PairSearch](../formal/GoldbachTm/Tm24/PairSearch.lean) proves that a failed pair
  advances the split, a successful pair increases the even number, and exhaustion
  without a pair halts.
- [Correctness](../formal/GoldbachTm/Tm24/Correctness.lean) reaches a least
  counterexample if one exists and rules out halting if every even input succeeds.

The headline axiom report contains only `propext`, `Classical.choice` and
`Quot.sound`. There is no `sorryAx`, project-specific axiom, or native-computation
axiom in that theorem's dependencies. The Python and C++ tools are not part of
its trusted proof path.

## Search and independent checks

The replay considers 48 ordered pairs of similar scan states, each direct merge,
and every repair consisting of replacing one further surviving transition by a
non-halting transition to a surviving state. This evaluates 218,976 candidates.
Primality and first pair-boundary checks screen the arithmetic. Candidates that
pass are tried from each surviving state on a blank tape, then checked on outer
loop cases. Only a bootstrap reaching the canonical boundary for 4 is accepted.

There are seven distinct finite-test survivors, all removing original state 22
and starting in state 18. Candidate 6, whose changed edge enters state 10, is the
one selected and formally proved. Merely passing whole-number examples was too
weak: wrong machines can advance through many even inputs. The final search
therefore checks prime/composite exits and the *first* pair boundary, including
composite pairs, before accepting a survivor.

The search has a bounded tape, a ones-count cap and per-fixture step budgets.
These are screening constraints, not lower bounds or proof assumptions. Exact
counts and limits are in [the search manifest](../reference/scan-sharing.json).

The independent Python verifier checks 256 primality cases, 1,056 growth inputs,
199 pair boundaries, 63 even boundaries, 13 synthetic odd no-pair inputs, and a
million blank-tape steps. It also compares the extracted 24-state Lean table with
the stated one-edge change and state deletion. [Its saved report](../reference/verification24.json)
is reproducible. Synthetic odd cases validate a phase's halting behavior; they
are not claimed counterexamples to Goldbach's conjecture.

## Baseline obstruction versus this construction

The [baseline audit](BASELINE.md) ruled out direct state-only quotients preserving
every step. This construction changes a transition, performs a different number
of steps through a different intermediate tape layout, and changes the initial
state. It therefore lies outside that obstruction. It establishes a 24-state
upper bound, not minimality.
