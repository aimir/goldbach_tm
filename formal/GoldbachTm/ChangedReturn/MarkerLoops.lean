/- Adapted from Yijun Leng, goldbach_tm (Apache-2.0).
   Changed-return arithmetic fragment; separate from the accepted Tm24 construction. -/
-- some lemmas tm31 doesn't contain

import GoldbachTm.ChangedReturn.Machine
import GoldbachTm.ChangedReturn.LocalTransitions

namespace ChangedReturn

variable {caller : Machine} {start : Cfg}

/-- Erase a leftward run and stop at its zero boundary in state 7. -/
theorem lemma7 (k : ℕ): ∀ (i : ℕ) (l r : List Γ),
run caller start i = some ⟨⟨7, by omega⟩, ⟨Γ.one, Turing.ListBlank.mk (List.replicate k Γ.one ++ List.cons Γ.zero l), Turing.ListBlank.mk r⟩⟩ →
run caller start (i + k + 1) = some ⟨⟨7, by omega⟩, ⟨Γ.zero, Turing.ListBlank.mk l, Turing.ListBlank.mk (List.replicate (k+1) Γ.zero ++ r)⟩⟩ := by
induction k with (intros i l r h; simp_all)
| zero => forwardR h
          rw [← h]
          ring_nf
| succ k induction_step =>
            forwardR h
            apply induction_step at h
            ring_nf at *
            simp! [h]
            rw [List.append_cons]
            rw [← List.replicate_succ']
            ring_nf

/-- Erase a leftward run and return through state 9 without setting the boundary bit. -/
theorem lemma8 (k : ℕ): ∀ (i : ℕ) (l r : List Γ),
run caller start i = some ⟨⟨8, by omega⟩, ⟨Γ.one, Turing.ListBlank.mk (List.replicate k Γ.one ++ List.cons Γ.zero l), Turing.ListBlank.mk r⟩⟩ →
run caller start (i + k + 2) = some ⟨⟨9, by omega⟩, ⟨Γ.zero, Turing.ListBlank.mk (Γ.zero :: l), Turing.ListBlank.mk (List.replicate k Γ.zero ++ r)⟩⟩ := by
induction k with (intros i l r h; simp_all)
| zero => iterate 2 forwardR h
          rw [← h]
          ring_nf
| succ k induction_step =>
            forwardR h
            apply induction_step at h
            ring_nf at *
            simp! [h]
            rw [List.append_cons]
            rw [← List.replicate_succ']
            ring_nf

/-- Fill a rightward zero run with ones to restore a unary counter. -/
theorem lemma10 (k : ℕ): ∀ (i : ℕ) (l r : List Γ),
run caller start i = some ⟨⟨10, by omega⟩, ⟨Γ.zero, Turing.ListBlank.mk l, Turing.ListBlank.mk (List.replicate k Γ.zero ++ List.cons Γ.one r) ⟩⟩ →
run caller start (i + k + 1) = some ⟨⟨10, by omega⟩, ⟨Γ.one, Turing.ListBlank.mk (List.replicate (k+1) Γ.one ++ l), Turing.ListBlank.mk r⟩⟩ := by
induction k with (intros i l r h; simp_all)
| zero => forwardR h
          rw [← h]
          ring_nf
| succ k induction_step =>
            specialize induction_step (i+1) (List.cons Γ.one l) r
            have g : i + (k+1) +1 = i + 1 + k + 1 := by omega
            rw [g, induction_step]
            . simp [List.replicate_succ' (k+1)]
            . simp! [run, h, step, Turing.Tape.write, Turing.Tape.move]

/-- Erase the remaining left counter and reach its zero boundary. -/
theorem lemma_6_to_7 (i : ℕ) (l1: ℕ) (l r : List Γ)
(h :
run caller start i = some ⟨⟨6, by omega⟩, ⟨Γ.one,
  Turing.ListBlank.mk (List.replicate l1 Γ.one ++ List.cons Γ.zero l),
  Turing.ListBlank.mk r,
  ⟩⟩) :
∃ j>i, run caller start j = some ⟨⟨7, by omega⟩, ⟨Γ.zero,
    Turing.ListBlank.mk l,
    Turing.ListBlank.mk (List.replicate (l1+1) Γ.zero ++ r),
    ⟩⟩
:= by
forwardR h
cases l1 with
| zero => use (1+i)
          simp [h]
| succ l1 => simp! at h
             apply lemma7 at h
             use (1+i+l1 + 1)
             simp [h]
             constructor
             . omega
             . rw [List.append_cons, ← List.replicate_succ']

/-- Pass the separator and rebuild an erased counter while moving right. -/
theorem lemma_9_to_10 (i : ℕ) (r1: ℕ) (l r : List Γ)
(h :
run caller start i = some ⟨⟨9, by omega⟩, ⟨Γ.zero,
  Turing.ListBlank.mk l,
  Turing.ListBlank.mk (List.replicate r1 Γ.zero ++ List.cons Γ.one r),
  ⟩⟩) :
∃ j>i, run caller start j = some ⟨⟨10, by omega⟩, ⟨Γ.one,
    Turing.ListBlank.mk (List.replicate r1 Γ.one ++ Γ.zero :: l),
    Turing.ListBlank.mk r,
    ⟩⟩
:= by
forwardR h
cases r1 with simp_all
| zero => use (1+i)
          simp [h]
| succ l1 => simp! at h
             apply lemma10 at h
             use (1+i+l1 + 1)
             simp [h]
             omega

end ChangedReturn
