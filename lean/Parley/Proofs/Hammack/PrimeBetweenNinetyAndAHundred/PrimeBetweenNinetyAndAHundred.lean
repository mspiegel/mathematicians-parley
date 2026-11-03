module

public import Tactics

/-! Written from proofs/hammack/prime-between-ninety-and-a-hundred.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.PrimeBetweenNinetyAndAHundred.PrimeBetweenNinetyAndAHundred

theorem prime_between_ninety_and_a_hundred :
    (∃ p : ℕ, 0 < p ∧ ((Nat.Prime p ∧ 90 < (p : ℤ)) ∧ (p : ℤ) < 100)) := by
  -- 1. inspection
  have s1 : Nat.Prime (97 : ℤ).toNat := by parley_side
  -- 2. arithmetic
  have s2 : (90 : ℤ) < 97 := by parley_arith
  -- 3. arithmetic
  have s3 : (97 : ℤ) < 100 := by parley_arith
  -- 4. exhibit, from 1, 2, 3
  have s4 : ∃ p : ℕ, 0 < p ∧ ((Nat.Prime p ∧ 90 < (p : ℤ)) ∧ (p : ℤ) < 100) := ⟨97, by parley_side, ⟨⟨by parley_side, by parley_side⟩, by parley_side⟩⟩
  all_goals exact s4

end Parley.Proofs.Hammack.PrimeBetweenNinetyAndAHundred.PrimeBetweenNinetyAndAHundred
