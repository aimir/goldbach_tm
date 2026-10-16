import GoldbachTm.Basic
import Mathlib.Data.Nat.Prime.Basic

/-! Kernel-checked finite Goldbach cases for a later blank-tape initialization.
The witness list is data; ordinary `decide` checks every entry. -/

namespace Goldbach

-- This bounded trial-divisor decision procedure reduces efficiently in the kernel.
attribute [local instance] Nat.decidablePrime1

private def prefixWitnesses : List (ℕ × ℕ) := [
  (2, 2), (3, 3), (3, 5), (3, 7), (5, 7), (3, 11),
  (3, 13), (5, 13), (3, 17), (3, 19), (5, 19), (3, 23),
  (5, 23), (7, 23), (3, 29), (3, 31), (5, 31), (7, 31),
  (3, 37), (5, 37), (3, 41), (3, 43), (5, 43), (3, 47),
  (5, 47), (7, 47), (3, 53), (5, 53), (7, 53), (3, 59),
  (3, 61), (5, 61), (7, 61), (3, 67), (5, 67), (3, 71),
  (3, 73), (5, 73), (7, 73), (3, 79), (5, 79), (3, 83),
  (5, 83), (7, 83), (3, 89), (5, 89), (7, 89), (19, 79),
  (3, 97), (5, 97), (3, 101), (3, 103), (5, 103), (3, 107),
  (3, 109), (5, 109), (3, 113), (5, 113), (7, 113), (13, 109),
  (11, 113), (13, 113), (19, 109), (3, 127), (5, 127), (3, 131),
  (5, 131), (7, 131), (3, 137), (3, 139), (5, 139), (7, 139),
  (11, 137), (11, 139), (3, 149), (3, 151), (5, 151), (7, 151),
  (3, 157), (5, 157), (7, 157), (3, 163), (5, 163), (3, 167),
  (5, 167), (7, 167), (3, 173), (5, 173), (7, 173), (3, 179),
  (3, 181), (5, 181), (7, 181), (11, 179), (11, 181), (3, 191),
  (3, 193), (5, 193), (3, 197), (3, 199), (5, 199), (7, 199),
  (11, 197), (11, 199), (13, 199), (3, 211), (5, 211), (7, 211),
  (23, 197), (11, 211), (13, 211), (3, 223), (5, 223), (3, 227),
  (3, 229), (5, 229), (3, 233), (5, 233), (7, 233), (3, 239),
  (3, 241), (5, 241), (7, 241), (11, 239), (11, 241), (3, 251),
  (5, 251)]

set_option maxRecDepth 10000 in
private theorem prefixWitnesses_valid : ∀ n : Fin 127,
    let w := prefixWitnesses[n.val]!
    w.1 + w.2 = 2*n.val+4 ∧ Nat.Prime w.1 ∧ Nat.Prime w.2 := by
  decide

/-- Every even instance from 4 through 256 has an explicit prime pair. -/
theorem verified_prefix (n : ℕ) (hn : n < 127) : Goldbach (2*n+4) := by
  have h := prefixWitnesses_valid ⟨n, hn⟩
  exact ⟨_, _, h⟩

/-- Skipping a verified finite prefix preserves the exact counterexample proposition. -/
theorem counterexample_iff_from (b : ℕ) (hb : b ≤ 127) :
    (∃ n, ¬ Goldbach (2*n+4)) ↔
      (∃ n, ¬ Goldbach (2*n+(2*b+4))) := by
  constructor
  · rintro ⟨n, hn⟩
    have hnb : b ≤ n := by
      by_contra h
      exact hn (verified_prefix n (by omega))
    refine ⟨n-b, ?_⟩
    have he : 2*(n-b)+(2*b+4) = 2*n+4 := by omega
    simpa only [he] using hn
  · rintro ⟨n, hn⟩
    refine ⟨n+b, ?_⟩
    have he : 2*(n+b)+4 = 2*n+(2*b+4) := by omega
    simpa only [he] using hn

/-- In particular, startup at 10 may omit the verified instances 4, 6 and 8. -/
theorem counterexample_iff_from_ten :
    (∃ n, ¬ Goldbach (2*n+4)) ↔ (∃ n, ¬ Goldbach (2*n+10)) := by
  simpa using counterexample_iff_from 3 (by decide)

end Goldbach
