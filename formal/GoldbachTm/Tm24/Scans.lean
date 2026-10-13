/- Adapted from Yijun Leng, goldbach_tm (Apache-2.0).
   Updated for the 24-state table and initialization; see reference/upstream.json. -/
-- theorem of recursive states
-- all these states' usage is to search 0
import GoldbachTm.Tm24.Machine

namespace Tm24

-- left
/-- Scan k+1 ones left in state 13, preserving them and stopping at zero; a state-specific wrapper used by the arithmetic proofs. -/
theorem rec13 (k : ℕ): ∀ (i : ℕ) (l r : List Γ),
nth_cfg i = some ⟨⟨13, by omega⟩, ⟨Γ.one, Turing.ListBlank.mk (List.replicate k Γ.one ++ List.cons Γ.zero l), Turing.ListBlank.mk r⟩⟩ →
nth_cfg (i + k + 1) = some ⟨⟨13, by omega⟩, ⟨Γ.zero, Turing.ListBlank.mk l, Turing.ListBlank.mk (List.replicate (k+1) Γ.one ++ r)⟩⟩ := by
induction k with intros i l r h
| zero => simp [nth_cfg, h, step, machine, Turing.Tape.write, Turing.Tape.move]
| succ k induction_step =>
            specialize induction_step (i+1) l (List.cons Γ.one r)
            have g : i + (k+1) +1 = i + 1 + k + 1 := by omega
            rw [g, induction_step]
            . simp [List.replicate_succ' (k+1)]
            . simp! [nth_cfg, h, step, machine, Turing.Tape.write, Turing.Tape.move]

/-- Scan k+1 ones left in state 14, preserving them and stopping at zero; a state-specific wrapper used by the arithmetic proofs. -/
theorem rec14 (k : ℕ): ∀ (i : ℕ) (l r : List Γ),
nth_cfg i = some ⟨⟨14, by omega⟩, ⟨Γ.one, Turing.ListBlank.mk (List.replicate k Γ.one ++ List.cons Γ.zero l), Turing.ListBlank.mk r⟩⟩ →
nth_cfg (i + k + 1) = some ⟨⟨14, by omega⟩, ⟨Γ.zero, Turing.ListBlank.mk l, Turing.ListBlank.mk (List.replicate (k+1) Γ.one ++ r)⟩⟩ := by
induction k with intros i l r h
| zero => simp [nth_cfg, h, step, machine, Turing.Tape.write, Turing.Tape.move]
| succ k induction_step =>
            specialize induction_step (i+1) l (List.cons Γ.one r)
            have g : i + (k+1) +1 = i + 1 + k + 1 := by omega
            rw [g, induction_step]
            . simp [List.replicate_succ' (k+1)]
            . simp! [nth_cfg, h, step, machine, Turing.Tape.write, Turing.Tape.move]

/-- Scan k+1 ones left in state 16, preserving them and stopping at zero; a state-specific wrapper used by the arithmetic proofs. -/
theorem rec16 (k : ℕ): ∀ (i : ℕ) (l r : List Γ),
nth_cfg i = some ⟨⟨16, by omega⟩, ⟨Γ.one, Turing.ListBlank.mk (List.replicate k Γ.one ++ List.cons Γ.zero l), Turing.ListBlank.mk r⟩⟩ →
nth_cfg (i + k + 1) = some ⟨⟨16, by omega⟩, ⟨Γ.zero, Turing.ListBlank.mk l, Turing.ListBlank.mk (List.replicate (k+1) Γ.one ++ r)⟩⟩ := by
induction k with intros i l r h
| zero => simp [nth_cfg, h, step, machine, Turing.Tape.write, Turing.Tape.move]
| succ k induction_step =>
            specialize induction_step (i+1) l (List.cons Γ.one r)
            have g : i + (k+1) +1 = i + 1 + k + 1 := by omega
            rw [g, induction_step]
            . simp [List.replicate_succ' (k+1)]
            . simp! [nth_cfg, h, step, machine, Turing.Tape.write, Turing.Tape.move]

/-- Scan k+1 ones left in state 18, preserving them and stopping at zero; a state-specific wrapper used by the arithmetic proofs. -/
theorem rec18 (k : ℕ): ∀ (i : ℕ) (l r : List Γ),
nth_cfg i = some ⟨⟨18, by omega⟩, ⟨Γ.one, Turing.ListBlank.mk (List.replicate k Γ.one ++ List.cons Γ.zero l), Turing.ListBlank.mk r⟩⟩ →
nth_cfg (i + k + 1) = some ⟨⟨18, by omega⟩, ⟨Γ.zero, Turing.ListBlank.mk l, Turing.ListBlank.mk (List.replicate (k+1) Γ.one ++ r)⟩⟩ := by
induction k with intros i l r h
| zero => simp [nth_cfg, h, step, machine, Turing.Tape.write, Turing.Tape.move]
| succ k induction_step =>
            specialize induction_step (i+1) l (List.cons Γ.one r)
            have g : i + (k+1) +1 = i + 1 + k + 1 := by omega
            rw [g, induction_step]
            . simp [List.replicate_succ' (k+1)]
            . simp! [nth_cfg, h, step, machine, Turing.Tape.write, Turing.Tape.move]

/-- Scan k+1 ones left in state 20, preserving them and stopping at zero; a state-specific wrapper used by the arithmetic proofs. -/
theorem rec20 (k : ℕ): ∀ (i : ℕ) (l r : List Γ),
nth_cfg i = some ⟨⟨20, by omega⟩, ⟨Γ.one, Turing.ListBlank.mk (List.replicate k Γ.one ++ List.cons Γ.zero l), Turing.ListBlank.mk r⟩⟩ →
nth_cfg (i + k + 1) = some ⟨⟨20, by omega⟩, ⟨Γ.zero, Turing.ListBlank.mk l, Turing.ListBlank.mk (List.replicate (k+1) Γ.one ++ r)⟩⟩ := by
induction k with intros i l r h
| zero => simp [nth_cfg, h, step, machine, Turing.Tape.write, Turing.Tape.move]
| succ k induction_step =>
            specialize induction_step (i+1) l (List.cons Γ.one r)
            have g : i + (k+1) +1 = i + 1 + k + 1 := by omega
            rw [g, induction_step]
            . simp [List.replicate_succ' (k+1)]
            . simp! [nth_cfg, h, step, machine, Turing.Tape.write, Turing.Tape.move]

/-- Scan k+1 ones left in state 22, preserving them and stopping at zero; a state-specific wrapper used by the arithmetic proofs. -/
theorem rec22 (k : ℕ): ∀ (i : ℕ) (l r : List Γ),
nth_cfg i = some ⟨⟨22, by omega⟩, ⟨Γ.one, Turing.ListBlank.mk (List.replicate k Γ.one ++ List.cons Γ.zero l), Turing.ListBlank.mk r⟩⟩ →
nth_cfg (i + k + 1) = some ⟨⟨22, by omega⟩, ⟨Γ.zero, Turing.ListBlank.mk l, Turing.ListBlank.mk (List.replicate (k+1) Γ.one ++ r)⟩⟩ := by
induction k with intros i l r h
| zero => simp [nth_cfg, h, step, machine, Turing.Tape.write, Turing.Tape.move]
| succ k induction_step =>
            specialize induction_step (i+1) l (List.cons Γ.one r)
            have g : i + (k+1) +1 = i + 1 + k + 1 := by omega
            rw [g, induction_step]
            . simp [List.replicate_succ' (k+1)]
            . simp! [nth_cfg, h, step, machine, Turing.Tape.write, Turing.Tape.move]

--right
/-- Scan k+1 ones right in state 11, preserving them and stopping at zero; a state-specific wrapper used by the arithmetic proofs. -/
theorem rec11 (k : ℕ): ∀ (i : ℕ) (l r : List Γ),
nth_cfg i = some ⟨⟨11, by omega⟩, ⟨Γ.one, Turing.ListBlank.mk l, Turing.ListBlank.mk (List.replicate k Γ.one ++ List.cons Γ.zero r) ⟩⟩ →
nth_cfg (i + k + 1) = some ⟨⟨11, by omega⟩, ⟨Γ.zero, Turing.ListBlank.mk (List.replicate (k+1) Γ.one ++ l), Turing.ListBlank.mk r⟩⟩ := by
induction k with intros i l r h
| zero => simp [nth_cfg, h, step, machine, Turing.Tape.write, Turing.Tape.move]
| succ k induction_step =>
            specialize induction_step (i+1) (List.cons Γ.one l) r
            have g : i + (k+1) +1 = i + 1 + k + 1 := by omega
            rw [g, induction_step]
            . simp [List.replicate_succ' (k+1)]
            . simp! [nth_cfg, h, step, machine, Turing.Tape.write, Turing.Tape.move]

/-- Scan k+1 ones right in state 19, preserving them and stopping at zero; a state-specific wrapper used by the arithmetic proofs. -/
theorem rec19 (k : ℕ): ∀ (i : ℕ) (l r : List Γ),
nth_cfg i = some ⟨⟨19, by omega⟩, ⟨Γ.one, Turing.ListBlank.mk l, Turing.ListBlank.mk (List.replicate k Γ.one ++ List.cons Γ.zero r) ⟩⟩ →
nth_cfg (i + k + 1) = some ⟨⟨19, by omega⟩, ⟨Γ.zero, Turing.ListBlank.mk (List.replicate (k+1) Γ.one ++ l), Turing.ListBlank.mk r⟩⟩ := by
induction k with intros i l r h
| zero => simp [nth_cfg, h, step, machine, Turing.Tape.write, Turing.Tape.move]
| succ k induction_step =>
            specialize induction_step (i+1) (List.cons Γ.one l) r
            have g : i + (k+1) +1 = i + 1 + k + 1 := by omega
            rw [g, induction_step]
            . simp [List.replicate_succ' (k+1)]
            . simp! [nth_cfg, h, step, machine, Turing.Tape.write, Turing.Tape.move]

/-- Scan k+1 ones right in state 21, preserving them and stopping at zero; a state-specific wrapper used by the arithmetic proofs. -/
theorem rec21 (k : ℕ): ∀ (i : ℕ) (l r : List Γ),
nth_cfg i = some ⟨⟨21, by omega⟩, ⟨Γ.one, Turing.ListBlank.mk l, Turing.ListBlank.mk (List.replicate k Γ.one ++ List.cons Γ.zero r) ⟩⟩ →
nth_cfg (i + k + 1) = some ⟨⟨21, by omega⟩, ⟨Γ.zero, Turing.ListBlank.mk (List.replicate (k+1) Γ.one ++ l), Turing.ListBlank.mk r⟩⟩ := by
induction k with intros i l r h
| zero => simp [nth_cfg, h, step, machine, Turing.Tape.write, Turing.Tape.move]
| succ k induction_step =>
            specialize induction_step (i+1) (List.cons Γ.one l) r
            have g : i + (k+1) +1 = i + 1 + k + 1 := by omega
            rw [g, induction_step]
            . simp [List.replicate_succ' (k+1)]
            . simp! [nth_cfg, h, step, machine, Turing.Tape.write, Turing.Tape.move]

end Tm24
