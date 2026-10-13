# Formal proof of the 24-state machine

**The default Lean build proves the blank-tape halting equivalence for the literal
24-state machine.** Start with [GoldbachTm.lean](GoldbachTm.lean): its headline
statement spells out the counterexample using `Nat.Prime`.

The [23-state experiments](../docs/SEARCH.md) have not produced an accepted
replacement. The machine and headline theorem here remain the verified 24-state result.

The transition table, state type `Fin 24`, blank-tape initialization in state 18,
execution semantics and 25-step startup lemma are in
[Machine.lean](GoldbachTm/Tm24/Machine.lean). `none` is the halting outcome.
`nth_cfg` begins with an empty input, so the theorem assumes no prewritten tape.

## Proof flow

1. **Machine:** the literal table and initialization.
2. **Scans, LocalTransitions, MarkerLoops:** movements and marker operations on
   arbitrary unary blocks; these support the arithmetic argument.
3. **Primality:** modular counters test trial divisors; prime and composite exits
   restore the input and preserve the surrounding tape.
4. **Growth:** the new reusable path joins two unary blocks and adds two ones.
5. **PairSearch:** failed pairs advance the split; a successful pair grows the
   outer input; exhausting all splits halts.
6. **Correctness:** earlier successes reach a least counterexample, if any;
   success for every even input prevents halting.
7. **GoldbachTm.lean:** combines the two directions into the headline equivalence.

The [module guide](GoldbachTm/Tm24/README.md) identifies the main intermediate
lemmas. Short repeated scan lemmas are wrappers for different concrete states;
they keep the arithmetic proofs close to the transition table.

## Build and inspect

With elan installed:

```sh
cd formal
lake build
lake env lean CheckAxioms.lean
```

The pin is `leanprover/lean4:v4.14.0-rc2`; `lake-manifest.json` pins mathlib and its
dependencies. The first build requires network access. An optional command to
fetch the targeted mathlib cache before building is:

```sh
lake exe cache get Mathlib/Computability/TuringMachine.lean Mathlib/Data/Nat/ModEq.lean Mathlib/Data/Nat/Prime/Basic.lean Mathlib/Tactic/Ring/RingNF.lean
```

The default build completed successfully. The headline theorem depends only on
`propext`, `Classical.choice` and `Quot.sound`; no `sorryAx`, additional project
axiom or native-computation axiom appears. The Python/C++ tools are not trusted
by the Lean proof. [The verification record](../reference/proof24.json) pins the
checked source hashes and commands.

`lake exe sim24` runs the optional streaming simulator until interrupted.

## Provenance

The proof adapts Yijun Leng's Apache-2.0-licensed 25-state development, pinned to
commit `6cd292062516a0a14ea1b34f2ab75154cae7ab1e` of
[lengyijun/goldbach_tm](https://github.com/lengyijun/goldbach_tm).
The shared `Basic`, `Format` and `ListBlank` files are unchanged. The concrete
machine, initialization and pair-success proof are updated; `Growth` is new.
The unused `never_halt` corollary and removed scan state's lemma are omitted.

The superseded full proof is not duplicated. Its original transition source is
retained in [reference/upstream](../reference/upstream/README.md) for computational
baseline checks. See [the provenance manifest](../reference/upstream.json) for
source mappings, original hashes and unmodified-file hashes. The [license](../LICENSE)
is preserved at the repository root.
