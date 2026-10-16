import GoldbachTm.ChangedReturn.Adapter.Machine

namespace ChangedReturn.Adapter

/-- Scan k+1 ones left in state 22, preserving them and stopping at zero; a state-specific wrapper used by the arithmetic proofs. -/
theorem rec22 (k : ℕ): ∀ (i : ℕ) (l r : List Γ),
run caller start i = some ⟨⟨22, by omega⟩, ⟨Γ.one, Turing.ListBlank.mk (List.replicate k Γ.one ++ List.cons Γ.zero l), Turing.ListBlank.mk r⟩⟩ →
run caller start (i + k + 1) = some ⟨⟨22, by omega⟩, ⟨Γ.zero, Turing.ListBlank.mk l, Turing.ListBlank.mk (List.replicate (k+1) Γ.one ++ r)⟩⟩ := by
induction k with intros i l r h
| zero => simp [run, h, step, Turing.Tape.write, Turing.Tape.move]
| succ k induction_step =>
            specialize induction_step (i+1) l (List.cons Γ.one r)
            have g : i + (k+1) +1 = i + 1 + k + 1 := by omega
            rw [g, induction_step]
            . simp [List.replicate_succ' (k+1)]
            . simp! [run, h, step, Turing.Tape.write, Turing.Tape.move]

/-- Scan k+1 ones right in state 21, preserving them and stopping at zero; a state-specific wrapper used by the arithmetic proofs. -/
theorem rec21 (k : ℕ): ∀ (i : ℕ) (l r : List Γ),
run caller start i = some ⟨⟨21, by omega⟩, ⟨Γ.one, Turing.ListBlank.mk l, Turing.ListBlank.mk (List.replicate k Γ.one ++ List.cons Γ.zero r) ⟩⟩ →
run caller start (i + k + 1) = some ⟨⟨21, by omega⟩, ⟨Γ.zero, Turing.ListBlank.mk (List.replicate (k+1) Γ.one ++ l), Turing.ListBlank.mk r⟩⟩ := by
induction k with intros i l r h
| zero => simp [run, h, step, Turing.Tape.write, Turing.Tape.move]
| succ k induction_step =>
            specialize induction_step (i+1) (List.cons Γ.one l) r
            have g : i + (k+1) +1 = i + 1 + k + 1 := by omega
            rw [g, induction_step]
            . simp [List.replicate_succ' (k+1)]
            . simp! [run, h, step, Turing.Tape.write, Turing.Tape.move]

end ChangedReturn.Adapter
