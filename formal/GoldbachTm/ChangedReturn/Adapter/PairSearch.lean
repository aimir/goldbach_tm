/- Adapted from Yijun Leng, goldbach_tm (Apache-2.0).
   Compatibility caller for the changed-return fragment; this construction still has 24 states. -/
-- PDP is short for "prime board prime"
import GoldbachTm.ChangedReturn.Adapter.Machine
import GoldbachTm.ChangedReturn.Adapter.Scans
import GoldbachTm.ChangedReturn.Adapter.Growth
import Mathlib.Data.Nat.Prime.Defs

namespace ChangedReturn.Adapter

-- l1 : count of 1 on the left
-- r1 : count of 1 on the right
/-- A failed prime pair advances the split by one while restoring the canonical pair layout. -/
theorem lemma_17 (i l1 r1: ℕ)
(hp : ¬ Nat.Prime (l1+1) \/ ¬ Nat.Prime (r1+1))
(g :
run caller start i = some ⟨⟨17, by omega⟩, ⟨Γ.one, Turing.ListBlank.mk (List.replicate (l1+1) Γ.one), Turing.ListBlank.mk (List.replicate (r1+1) Γ.one)⟩⟩
):
∃ j>i, run caller start j = some ⟨⟨17, by omega⟩, ⟨Γ.one, Turing.ListBlank.mk (List.replicate l1 Γ.one), Turing.ListBlank.mk (List.replicate (r1+2) Γ.one)⟩⟩ := by
forwardR g
forwardR g
forwardR g
by_cases hr1 : Nat.Prime (r1+1)
. refine (?_ ∘ (prime_20 (caller := caller) (start := start) (3+i) r1 (Γ.one :: List.replicate l1 Γ.one) [])) ?_
  . intros g
    specialize g hr1
    obtain ⟨j, _, g⟩ := g
    iterate 2 forwardR g
    have h : Turing.ListBlank.mk (List.replicate l1 Γ.one) = Turing.ListBlank.mk (List.replicate l1 Γ.one ++ [Γ.zero]) := by
      simp! [g, Turing.ListBlank.mk]
      rw [Quotient.eq'']
      left
      use 1
      tauto
    rw [h] at g
    apply (rec22 l1 (2+j) []) at g
    forwardR g
    have h : ¬ Nat.Prime (l1+1) := by tauto
    apply (n_prime_16 (caller := caller) (start := start)) at h
    pick_goal 5
    . rw [g]
      simp
      repeat any_goals apply And.intro
      all_goals rfl
    obtain ⟨m, _, h⟩ := h
    iterate 3 forwardR h
    apply rec21 at h
    forwardR h
    use (5+m+l1)
    constructor
    . omega
    . simp [h]
      repeat any_goals apply And.intro
      all_goals simp! [Turing.ListBlank.mk]
      all_goals rw [Quotient.eq'']
      all_goals right
      . use 2
        tauto
      . use 1
        simp
        tauto
  . simp! [g, Turing.ListBlank.mk]
    rw [Quotient.eq'']
    left
    use 1
    tauto
. apply (n_prime_16 (caller := caller) (start := start)) at hr1
  pick_goal 5
  . rw [g]
    simp
    repeat any_goals apply And.intro
    . rfl
    . simp! [Turing.ListBlank.mk]
      rw [Quotient.eq'']
      left
      use 1
      tauto
  obtain ⟨j, _, g⟩ := hr1
  forwardR g
  use (1+j)
  constructor
  . omega
  . simp! [g]
    simp! [Turing.ListBlank.mk]
    rw [Quotient.eq'']
    right
    use 1
    rw [← List.cons_append]
    rw [← List.replicate_succ]
    rw [← List.cons_append]
    rw [← List.replicate_succ]
    ring_nf
    tauto

-- +2
/-- A successful prime pair invokes grow_blocks to increase the outer number by two. -/
theorem both_prime (i l1 r1: ℕ)
(hpl : Nat.Prime (l1+1))
(hpr : Nat.Prime (r1+1))
(g :
run caller start i = some ⟨⟨17, by omega⟩, ⟨Γ.one, Turing.ListBlank.mk (List.replicate (l1+1) Γ.one), Turing.ListBlank.mk (List.replicate (r1+1) Γ.one)⟩⟩
) :
∃ j>i, run caller start j = some ⟨⟨21, by omega⟩, ⟨Γ.zero, Turing.ListBlank.mk (List.replicate (l1+r1+4) Γ.one), Turing.ListBlank.mk []⟩⟩ := by
forwardR g
forwardR g
forwardR g
apply (prime_20 (caller := caller) (start := start)) at hpr
pick_goal 5
. rw [g]
  simp
  constructor
  . rfl
  . simp! [Turing.ListBlank.mk]
    rw [Quotient.eq'']
    left
    use 1
    tauto
clear g
obtain ⟨j, _, g⟩ := hpr
iterate 2 forwardR g
have h : Turing.ListBlank.mk (List.replicate l1 Γ.one) = Turing.ListBlank.mk (List.replicate l1 Γ.one ++ [Γ.zero]) := by
  simp! [g, Turing.ListBlank.mk]
  rw [Quotient.eq'']
  left
  use 1
  tauto
rw [h] at g
apply (rec22 l1 (2+j) []) at g
forwardR g
apply (prime_20 (caller := caller) (start := start)) at hpl
pick_goal 5
. rw [g]
obtain ⟨m, hm, g⟩ := hpl
iterate 3 forwardR g
have z : Turing.ListBlank.mk [Γ.zero] = Turing.ListBlank.mk [] := mk_trailing_zero []
have h := grow_blocks (3+m) l1 (r1+1) (by
  simp only [← List.cons_append, ← List.append_assoc, mk_trailing_zero] at g
  simpa [List.replicate_succ, z] using g)
obtain ⟨j, hj, h⟩ := h
refine ⟨j, ?_, ?_⟩
· omega
· simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h


/-- If a suitable prime pair remains, the pair search reaches the next outer boundary. -/
theorem leap_17 (l1 : ℕ) : ∀ (i r1: ℕ),
l1 + r1 ≥ 2 →
Even (l1+r1) →
run caller start i = some ⟨⟨17, by omega⟩, ⟨Γ.one, Turing.ListBlank.mk (List.replicate (l1+1) Γ.one), Turing.ListBlank.mk (List.replicate (r1+1) Γ.one)⟩⟩ →
(∃ x y, x + y = l1 + r1 + 2 /\ Nat.Prime x /\ Nat.Prime y /\ (r1+1) ≤ x /\ x ≤ y) →
∃ j>i, run caller start j = some ⟨⟨21, by omega⟩, ⟨Γ.zero, Turing.ListBlank.mk (List.replicate (l1+r1+4) Γ.one), Turing.ListBlank.mk []⟩⟩
:= by
induction l1 with
| zero => omega
| succ l1 induction_step =>
  intros i r1 h _ g hpp
  by_cases hp : ¬ Nat.Prime (l1+2) \/ ¬ Nat.Prime (r1+1)
  . -- induction step
    apply lemma_17 at g
    any_goals tauto
    obtain ⟨j, _, g⟩ := g
    apply induction_step at g
    all_goals ring_nf at *
    any_goals assumption
    refine (?_ ∘ g) ?_
    . intros g
      obtain ⟨m, g₂⟩ := g
      use m
      ring_nf at *
      simp [g₂]
      omega
    . obtain ⟨x, y, _, _, _, _⟩ := hpp
      use! x, y
      repeat any_goals apply And.intro
      any_goals assumption
      any_goals omega
      by_cases x = r1+1
      any_goals omega
      subst x
      exfalso
      cases hp with
      | inl hp => apply hp
                  have : y = l1+2 := by omega
                  subst y
                  ring_nf at *
                  assumption
      | inr hp => apply hp
                  ring_nf at *
                  assumption
  . -- both prime
    apply both_prime at g
    all_goals tauto


/-- With no prime pair, the finite split search exhausts the left summand and halts. -/
theorem leap_17_halt (l1 : ℕ) : ∀ (i r1: ℕ),
l1 + r1 ≥ 2 →
run caller start i = some ⟨⟨17, by omega⟩, ⟨Γ.one, Turing.ListBlank.mk (List.replicate (l1+1) Γ.one), Turing.ListBlank.mk (List.replicate (r1+1) Γ.one)⟩⟩ →
(∀ x y, x + y = l1 + r1 + 2 /\ Nat.Prime x /\ Nat.Prime y → False) →
∃ j, run caller start j = none
:= by
induction l1 with
| zero =>
  intros i r1 h g hpp
  have hr1 : ∃ r2, r2 + 2 = r1 := by use (r1-2); omega
  obtain ⟨r2, _⟩ := hr1
  subst r1
  forwardR g
  forwardR g
  forwardR g
  rw [← List.replicate_succ] at g
  rw [← List.replicate_succ] at g
  by_cases hp : Nat.Prime (r2+3)
  . apply (prime_20 (caller := caller) (start := start)) at hp
    pick_goal 5
    . rw [g]
      simp
      constructor
      . rfl
      . simp! [Turing.ListBlank.mk]
        rw [Quotient.eq'']
        left
        use 1
        tauto
    obtain ⟨j, _, h⟩ := hp
    iterate 14 forwardR h
    use (14+j)
  . apply (n_prime_16 (caller := caller) (start := start)) at hp
    pick_goal 5
    . rw [g]
      simp
      constructor
      . rfl
      . simp! [Turing.ListBlank.mk]
        rw [Quotient.eq'']
        left
        use 1
        tauto
    obtain ⟨j, _, h⟩ := hp
    iterate 3 forwardR h
    use (3+j)
| succ l1 induction_step =>
    intros i r1 h g hpp
    apply lemma_17 at g
    . obtain ⟨j, _, g⟩ := g
      apply induction_step at g
      any_goals omega
      apply g
      ring_nf at hpp
      ring_nf
      assumption
    . specialize hpp (l1+2) (r1+1)
      ring_nf at hpp
      simp at hpp
      ring_nf
      tauto

end ChangedReturn.Adapter
