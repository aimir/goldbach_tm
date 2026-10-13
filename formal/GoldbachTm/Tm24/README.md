# Proof of the 24-state construction

The [headline theorem](../../GoldbachTm.lean) is the reading entry point. Its
literal definitions are in [Machine.lean](Machine.lean), followed by this flow:

| Module | Main result and role |
| --- | --- |
| [Machine](Machine.lean) | `machine` has type `Fin 24 → Γ → Option (Fin 24 × Stmt)`; `cfg25` initializes the boundary for 4. |
| [Scans](Scans.lean) | The `rec*` lemmas scan arbitrary runs in specific states. These repeated wrappers share a proof pattern but describe different transition-table entries. |
| [LocalTransitions](LocalTransitions.lean) | `lemma_10_to_11` moves the right separator; `lemma_15_to_18` returns after a failed divisor test. |
| [MarkerLoops](MarkerLoops.lean) | Erasing and restoring counters, plus the state-6 and state-9 entry paths. |
| [Primality](Primality.lean) | `step_10_pointer` and `end_10` maintain modular counters. `prime_20` and `n_prime_16` establish the complete primality interface. |
| [Growth](Growth.lean) | `grow_blocks` reuses the marker loop to combine arbitrary block lengths and add two ones, replacing the deleted state. |
| [PairSearch](PairSearch.lean) | `lemma_17` advances failed pairs, `both_prime` grows on success, and `leap_17`/`leap_17_halt` finish the finite pair search. |
| [Correctness](Correctness.lean) | Reach successive even boundaries, halt on a least counterexample, and exclude halting when every instance succeeds. |

Every main derived lemma has an explanatory docstring. The inherited names are
kept where they make correspondence with the upstream argument useful. `Sim24`
is an optional simulator and is not part of the theorem's proof dependency path.
