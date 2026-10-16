import GoldbachTm.Tm24.Correctness
import GoldbachTm.FinitePrefix

/-!
# A 24-state binary Turing machine for Goldbach's conjecture

This is the headline theorem checked by `lake build`. `Tm24.nth_cfg` executes
`Tm24.machine` from state 18 on an all-zero tape. `none` is the halting outcome.
The complete transition table and execution definitions are in `Tm24/Machine.lean`;
its working-state type is literally `Fin 24`. No extra initialization states,
nonblank input, or arithmetic oracle is assumed.
-/

/-- The blank-tape 24-state machine halts exactly when an even integer at least
four has no decomposition into two natural primes. -/
theorem Tm24.halts_iff_goldbach_counterexample :
    (∃ i, Tm24.nth_cfg i = none) ↔
    (∃ n : ℕ, ¬ ∃ p q : ℕ, p + q = 2*n+4 ∧ Nat.Prime p ∧ Nat.Prime q) :=
  ⟨Tm24.halt_lemma_rev, Tm24.halt_lemma'⟩
