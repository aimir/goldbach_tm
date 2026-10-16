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

/-- Exact local adapter contract: restore the erased first cell and skip its separator.
The helper may be any state whose zero branch supplies the specified second step. -/
theorem restore_prime_exit {caller : Machine} {start : Cfg}
    (helper : Fin 24)
    (hprime : machine caller 20 Γ.zero = some ⟨helper, ⟨Turing.Dir.left, Γ.one⟩⟩)
    (hhelper : machine caller helper Γ.zero = some ⟨22, ⟨Turing.Dir.left, Γ.zero⟩⟩)
    (i tail : ℕ) (l r : List Γ)
    (g : run caller start i = some (primeExit tail l r)) :
    run caller start (i+2) = some ⟨22, ⟨l.headI, Turing.ListBlank.mk l.tail,
      Turing.ListBlank.mk (Γ.zero :: (List.replicate (tail+1) Γ.one ++ Γ.zero :: r))⟩⟩ := by
  have h₁ : run caller start (i+1) = some ⟨helper, ⟨Γ.zero, Turing.ListBlank.mk l,
      Turing.ListBlank.mk (Γ.one :: (List.replicate tail Γ.one ++ Γ.zero :: r))⟩⟩ := by
    rw [run, g]
    simp [primeExit, step, hprime, Turing.Tape.write, Turing.Tape.move]
  rw [show i + 2 = (i+1)+1 by omega, run, h₁]
  simp [step, hhelper, Turing.Tape.write, Turing.Tape.move, List.replicate_succ]

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
