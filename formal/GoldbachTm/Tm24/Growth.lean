import GoldbachTm.Tm24.Primality

namespace Tm24

/-- A trailing blank does not change a represented tape half. -/
theorem mk_trailing_zero (l : List Γ) :
    Turing.ListBlank.mk (l ++ [Γ.zero]) = Turing.ListBlank.mk l := by
  apply Quotient.sound
  exact Or.inr ⟨1, by simp; rfl⟩

theorem mk_trailing_two_zeros (l : List Γ) :
    Turing.ListBlank.mk (l ++ [Γ.zero, Γ.zero]) = Turing.ListBlank.mk l := by
  simpa [List.append_assoc] using
    (mk_trailing_zero (l ++ [Γ.zero])).trans (mk_trailing_zero l)

attribute [local simp] mk_trailing_zero mk_trailing_two_zeros

/-- The existing marker-transfer loop joins two unary blocks and adds two ones.
This replaces the removed scan state; no primality assumption is needed. -/
theorem grow_blocks (i p q : ℕ)
    (g : nth_cfg i = some ⟨0, ⟨Γ.zero, Turing.ListBlank.mk [],
      Turing.ListBlank.mk (List.replicate (p+1) Γ.one ++ Γ.zero :: List.replicate q Γ.one)⟩⟩) :
    ∃ j > i, nth_cfg j = some ⟨21, ⟨Γ.zero,
      Turing.ListBlank.mk (List.replicate (p+q+3) Γ.one), Turing.ListBlank.mk []⟩⟩ := by
  have z1 := mk_trailing_zero []
  have z2 := mk_trailing_two_zeros []
  simp only [List.nil_append] at z1 z2
  rw [List.replicate_succ] at g
  forward g
  have h := end_10 q (1+i) 0 0 p [] []
  simp only [List.replicate_zero, List.nil_append] at h
  have g' : nth_cfg (1+i) = some ⟨10, ⟨Γ.one,
      Turing.ListBlank.mk [Γ.zero, Γ.zero],
      Turing.ListBlank.mk (List.replicate p Γ.one ++ Γ.zero ::
        (List.replicate q Γ.one ++ [Γ.zero]))⟩⟩ := by
    simpa only [← List.cons_append, ← List.append_assoc, mk_trailing_zero, z1, z2] using g
  specialize h g' Nat.modEq_one
  obtain ⟨j, hj, la, lb, g, _, heq⟩ := h
  have hla : la = 0 := by omega
  have hlb : lb = 0 := by omega
  subst la
  subst lb
  simp only [List.replicate_zero, List.nil_append] at g
  apply lemma_10_to_11 at g
  obtain ⟨k, g⟩ := g
  forward g
  forward g
  apply rec14 at g
  iterate 7 forward g
  repeat rw [← List.replicate_succ] at g
  rw [← mk_trailing_zero (List.replicate (p+q+1+1) Γ.one)] at g
  apply rec21 at g
  refine ⟨_, ?_, by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using g⟩
  omega

end Tm24
