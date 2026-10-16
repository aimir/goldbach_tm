/- Adapted from Yijun Leng, goldbach_tm (Apache-2.0).
   Changed-return arithmetic fragment; separate from the accepted Tm24 construction. -/
import GoldbachTm.ChangedReturn.Machine
import GoldbachTm.ChangedReturn.Scans

namespace ChangedReturn

variable {caller : Machine} {start : Cfg}

/-- Move the right separator across a unary block in one divisor-counter iteration. -/
theorem lemma_10_to_11 (i : ℕ) (r1: ℕ) (l r : List Γ)
(h :
run caller start i = some ⟨⟨10, by omega⟩, ⟨Γ.one,
  Turing.ListBlank.mk l,
  Turing.ListBlank.mk (List.replicate r1 Γ.one ++ List.cons Γ.zero r)⟩⟩) :

∃ j, run caller start (j + i) = some ⟨⟨11, by omega⟩, ⟨Γ.zero, Turing.ListBlank.mk (List.replicate r1 Γ.one ++ List.cons Γ.zero l), Turing.ListBlank.mk r⟩⟩
:= by
forwardR h
cases r1 with
| zero => use 1
          simp [h]
| succ r1 => apply rec11 at h
             use (r1 + 2)
             rw [← h]
             ring_nf

/-- Scan left after a failed divisibility test to begin restoring the trial-divisor layout. -/
theorem lemma_15_to_18 (i : ℕ) (l1: ℕ) (l r : List Γ)
(h :
run caller start i = some ⟨⟨15, by omega⟩, ⟨Γ.one,
  Turing.ListBlank.mk (List.replicate l1 Γ.one ++ List.cons Γ.zero l),
  Turing.ListBlank.mk r,
  ⟩⟩) :
∃ j, run caller start (j + i) = some ⟨⟨18, by omega⟩, ⟨Γ.zero,
    Turing.ListBlank.mk l,
    Turing.ListBlank.mk (List.replicate (l1+1) Γ.one ++ r),
    ⟩⟩
:= by
forwardR h
cases l1 with simp! [*, -run] at h
| zero => use 1
          simp [h]
| succ r1 =>  apply rec18 at h
              use (r1+2)
              ring_nf at *
              simp [h]
              rw [List.append_cons, ← List.replicate_succ']
              ring_nf

end ChangedReturn
