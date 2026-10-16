/- Adapted from Yijun Leng, goldbach_tm (Apache-2.0).
   Compatibility caller for the changed-return fragment; this construction still has 24 states. -/
import GoldbachTm.ChangedReturn.Adapter.Machine
import GoldbachTm.ChangedReturn.Adapter.Scans
import GoldbachTm.ChangedReturn.Adapter.PairSearch
import Mathlib.Data.Nat.Prime.Defs

namespace ChangedReturn.Adapter

/-- A successful Goldbach instance advances the canonical outer boundary by two. -/
theorem lemma_21 (n : ℕ) (i : ℕ)
(even_n : Even (n+2))
(g :
run caller start i = some ⟨⟨21, by omega⟩, ⟨Γ.zero, Turing.ListBlank.mk (List.replicate (n+4) Γ.one), Turing.ListBlank.mk []⟩⟩ )
( hpp : Goldbach (n+4)) :
∃ j>i, run caller start j = some ⟨⟨21, by omega⟩, ⟨Γ.zero, Turing.ListBlank.mk (List.replicate (n+4+2) Γ.one), Turing.ListBlank.mk []⟩⟩
:= by
forwardR g
repeat rw [← List.replicate_succ] at g
apply (leap_17 _ _ 0) at g
any_goals omega
any_goals assumption
refine (?_ ∘ g) ?_
. intros g
  obtain ⟨k, _, h⟩ := g
  use k
  constructor
  . omega
  . simp [h]
. obtain ⟨x, y, _, hx, hy⟩ := hpp
  by_cases x ≤ y
  . use! x, y
    repeat any_goals apply And.intro
    any_goals assumption
    apply Nat.Prime.two_le at hx
    omega
  . use! y, x
    repeat any_goals apply And.intro
    any_goals assumption
    any_goals omega
    apply Nat.Prime.two_le at hy
    omega

/-- Success of all earlier even instances guarantees reaching the next even boundary. -/
lemma never_halt_step (n : ℕ) :
(∀ i < n, Goldbach (2*i+4)) ->
∃ j, run caller start j = some ⟨⟨21, by omega⟩, ⟨Γ.zero, Turing.ListBlank.mk (List.replicate (2*n+4) Γ.one), Turing.ListBlank.mk []⟩⟩
 := by
induction n with
| zero =>
intros _
use 27
simp [cfg27]
| succ n induction_step =>
intros h
refine (?_ ∘ induction_step) ?_
. intros g
  obtain ⟨j, g⟩ := g
  specialize h n (by omega)
  apply lemma_21 at g
  . specialize g h
    obtain ⟨k, g⟩ := g
    use k
    simp [g]
    ring_nf
  . use (n+1)
    ring_nf
. intros i hi
  apply h i (by omega)

/-- Goldbach for every even input forces arbitrarily late successful boundaries, excluding halting. -/
theorem halt_lemma_rev' (h : ∀ n, Goldbach (2*n+4)) :
∀ i, run caller start i ≠ none := by
apply propagating_induction (fun i => run caller start i ≠ none) (fun i n => run caller start i = some ⟨⟨21, by omega⟩, ⟨Γ.zero, Turing.ListBlank.mk (List.replicate (2*n+4) Γ.one), Turing.ListBlank.mk []⟩⟩) 27
. simp [cfg27]
. intros i n g
  apply (lemma_21 (2*n)) at g
  . specialize g (h _)
    obtain ⟨j, g⟩ := g
    use j
    simp! [g]
  . use (n+1)
    ring_nf
. intros i n g j hij _
  have h₂ : ∀ k, run caller start (j+k) = none := by
    intro k
    induction k with
    | zero => tauto
    | succ k => simp! [run, ← add_assoc, *]
  specialize h₂ (i-j)
  have h₃ : j + (i-j) = i := by omega
  rw [h₃] at h₂
  rw [h₂] at g
  tauto

theorem halt_lemma':
(∃ n, ¬ Goldbach (2*n+4)) → (∃ i, run caller start i = none)
:= by
intros h
obtain ⟨j, hj⟩ := never_halt_step (Nat.find h) (λ i g =>
by rw [← Mathlib.Tactic.PushNeg.not_not_eq (Goldbach (2*i+4))]
   apply Nat.find_min h g
)
forwardR hj
repeat rw [← List.replicate_succ] at hj
apply (leap_17_halt _ _ 0) at hj
any_goals omega
apply hj
intros x y _
apply Nat.find_spec h
use! x, y

/-- Halting implies a counterexample, by contraposition of the non-halting direction. -/
theorem halt_lemma_rev :
(∃ i, run caller start i = none) → (∃ n, ¬ Goldbach (2*n+4))
:= by
intros h
by_contra! g
apply halt_lemma_rev' at g
tauto

/-- Complete composition check for the changed-return classifier and its helper caller.
This is a 24-state machine; state 3 supplies the extra prime-return adapter step. -/
theorem halts_iff_goldbach_counterexample :
    (∃ i, run caller start i = none) ↔
    (∃ n : ℕ, ¬ ∃ p q : ℕ, p + q = 2*n+4 ∧ Nat.Prime p ∧ Nat.Prime q) :=
  ⟨halt_lemma_rev, halt_lemma'⟩

end ChangedReturn.Adapter
