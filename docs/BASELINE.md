# Audit of the 25-state baseline

The current result is the [formally verified 24-state construction](REDUCTION.md).
This document records what the initial fixed-table audit ruled out.

## What is established

The pinned upstream project defines `Goldbach n` as the existence of natural
primes `x,y` with `x+y=n`. Its two final implication theorems establish

```lean
(∃ i, Tm25.nth_cfg i = none) ↔ (∃ n, ¬ Goldbach (2*n + 4))
```

The forward implication is `Tm25.halt_lemma_rev`; the reverse is
`Tm25.halt_lemma'`. These are in
[the pinned upstream Content.lean](https://github.com/lengyijun/goldbach_tm/blob/6cd292062516a0a14ea1b34f2ab75154cae7ab1e/GoldbachTm/Tm25/Content.lean). The equivalence above
combines those statements; it is not an additional compiled theorem in this
project. `nth_cfg` begins in state 0 on an all-zero tape. There are 25 working
states; a transition returning `none` halts. The original full proof was not rebuilt here; its adapted 24-state successor
has passed the Lean build.

The repository checked on 2026-10-08 advertises 25 states. An initial web search
found no better Goldbach construction; that is not an exhaustive certification of
current records. The upstream progression from 26 to 25 used an unreachable
branch and a changed transition before merging. Such transition changes go
beyond a direct quotient of a fixed transition table.

## Why ordinary merging is exhausted here

A literal blank-tape trace visits every non-halting `(state, read bit)` branch by
step 852, counting the initial configuration as step 0. The sole unvisited branch
is `(24,0)`, which halts. We do not assume it is unreachable: that would already
assume Goldbach's conjecture.

Suppose a new machine were obtained only by mapping old states to new states,
keeping each step's tape contents and head position. If two old states are
mapped together, their observed transitions on the same read bit must write the
same bit, move in the same direction, and map their successors together.

The audit starts with write/move conflicts and propagates successor conflicts.
Every one of the 300 unordered pairs of states becomes incompatible. It even
works with the halting branch left unconstrained. The report contains one reason
per pair, ordered so every successor dependency has already been established.
A separate checker replays the reachability witnesses and checks these reasons.
No SAT search is needed for this particular quotient problem.

This is a computationally checked obstruction to **state-only step-preserving
quotients**. It is not a lower bound on machines allowing different paths,
intermediate tapes, head positions, state-dependent representations, or running
times. There is no Lean proof of this obstruction in the current project.

## Other initial checks

Finite tape windows of radii 2 through 6 overapproximate all reachable tapes by
allowing either symbol at each newly exposed boundary. All 50 branch masks remain
possible at those radii. Their failure to remove the halting branch says nothing
about whether that branch is reachable.

For every state and initial read bit, the exact path enumerator checks every odd
length from 3 through 31. It branches on every initially unknown cell and rejects
any path that halts, changes another cell permanently, ends more than one cell
away, or disagrees with another symbolic path on its resulting transition.
There are no nontrivial all-input path-to-one-transition replacements in that
range. This does not cover invariant-dependent rewrites or replacements of one
multi-state fragment by another.

The independent arithmetic oracle checks inputs 1 through 128 at the primality
entry interface, both with blank surroundings and with nonzero surrounding tape.
It requires the correct prime/composite exit, exact head position, and exact
restoration of the entire tape. These 256 cases execute 16,371,996 transitions.

Outer-loop tests start at the canonical state-21 boundary. For each even input
from 4 through 64, they require the next canonical boundary representing `n+2`.
For the 13 odd inputs below 65 that have no prime-pair decomposition, they require
halting. The upstream no-pair phase lemma does not require evenness, so these are
useful negative fixtures. They are synthetic phase inputs and do not occur on the
blank-tape run. The tests would reject a candidate that merely keeps running.

## Search directions identified by this audit

Direction 1 produced the current 24-state result; directions 2 and 3 remain
possible avenues for further work.

1. **Share scans by changing their boundary conventions.** Six states
   (13, 14, 16, 18, 20, 23) share the same action on a run of ones: preserve each
   one and move left. Four states (11, 19, 21, 22) similarly scan right. Their
   zero exits differ, so they cannot simply be merged. Search small replacements
   that move an entry point, marker, or return convention and compensate at the
   callers. This led to reusing the arithmetic loop and changing the initial state,
   reaching 24 total working states without an adapter.
2. **Synthesize replacements inside the primality routine.** Its Lean lemmas
   describe unary blocks, moving markers, and modular arithmetic. Use these
   interfaces to generate examples for small bounded fragments, then search
   candidate tables with fewer states. Validate retained candidates over larger
   inputs and prove the parameterized fragment relation before claiming a new
   verified bound. Favor reuse of existing machine states over isolated routines
   that need extra dispatch or cleanup.
3. **Change the tape representation if local replacement stalls.** Consider
   different unary marker layouts or joint checking of complementary summands.
   Fewer arithmetic operations need not mean fewer machine states; the final
   literal transition table remains the objective.

Finite phase tests are screening tools. An accepted improvement still needs an
unbounded argument that it preserves both finding a counterexample and eventual
progress through all even inputs. A successful infinite-looking simulation alone
cannot establish either direction.
