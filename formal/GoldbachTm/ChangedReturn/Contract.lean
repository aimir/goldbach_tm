import GoldbachTm.ChangedReturn.Primality

namespace ChangedReturn

/-- A positive unary input, of value `tail + 1`, with arbitrary separated contexts. -/
def input (tail : ℕ) (l r : List Γ) : Cfg :=
  ⟨0, ⟨Γ.one, Turing.ListBlank.mk (Γ.zero :: l),
    Turing.ListBlank.mk (List.replicate tail Γ.one ++ Γ.zero :: r)⟩⟩

/-- The prime return erases just the first input cell and stops on that cell. -/
def primeExit (tail : ℕ) (l r : List Γ) : Cfg :=
  ⟨20, ⟨Γ.zero, Turing.ListBlank.mk (Γ.zero :: l),
    Turing.ListBlank.mk (List.replicate tail Γ.one ++ Γ.zero :: r)⟩⟩

/-- The composite return restores the whole input and stops on its left separator. -/
def compositeExit (tail : ℕ) (l r : List Γ) : Cfg :=
  ⟨16, ⟨Γ.zero, Turing.ListBlank.mk l,
    Turing.ListBlank.mk (List.replicate (tail+1) Γ.one ++ Γ.zero :: r)⟩⟩

/-- Unbounded arithmetic classification with strict progress, uniformly in every caller.
The caller supplies only transitions outside the arithmetic fragment. -/
theorem classifies (caller : Machine) (tail : ℕ) (l r : List Γ) :
    ∃ j > 0, run caller (input tail l r) j = some
      (if Nat.Prime (tail+1) then primeExit tail l r else compositeExit tail l r) := by
  classical
  by_cases hp : Nat.Prime (tail+1)
  · simpa [hp, primeExit] using prime_20 0 tail l r (by rfl) hp
  · simpa [hp, compositeExit] using n_prime_16 0 tail l r (by rfl) hp

/-- A caller that halts at either arithmetic return. -/
def stopCaller : Machine := fun _ _ => none

/-- In isolation the fragment always terminates on every positive unary input. -/
theorem terminates (tail : ℕ) (l r : List Γ) :
    ∃ j > 0, run stopCaller (input tail l r) j = none := by
  obtain ⟨j, hj, h⟩ := classifies stopCaller tail l r
  refine ⟨j+1, by omega, ?_⟩
  rw [run, h]
  have hp : machine stopCaller 20 Γ.zero = none := rfl
  have hc : machine stopCaller 16 Γ.zero = none := rfl
  split_ifs <;> simp [step, hp, hc, primeExit, compositeExit]

end ChangedReturn
