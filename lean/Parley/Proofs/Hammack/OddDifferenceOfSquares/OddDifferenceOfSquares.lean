module

public import Tactics
public import Parley.Items.Stdlib.Divisibility

/-! Written from proofs/hammack/odd-difference-of-squares.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.OddDifferenceOfSquares.OddDifferenceOfSquares

theorem odd_difference_of_squares (n : ℤ) (hH2 : Odd n) :
    (∃ a : ℤ, ∃ b : ℤ, n = a ^ 2 - b ^ 2) := by
  -- 1. obtain k: def:odd, from H2
  obtain ⟨k, s1⟩ := ((Parley.Items.Stdlib.Divisibility.def_odd (n := n))).mp (by parley_side)
  -- 2. calculation
  have s2 : n = (k + 1) ^ 2 - k ^ 2 := by
    calc n = 2 * k + 1 := by parley_side
      _ = (k + 1) ^ 2 - k ^ 2 := by parley_ring
  -- 3. exhibit, from 2
  have s3 : ∃ a : ℤ, ∃ b : ℤ, n = a ^ 2 - b ^ 2 := ⟨k + 1, k, by parley_side⟩
  all_goals exact s3

end Parley.Proofs.Hammack.OddDifferenceOfSquares.OddDifferenceOfSquares
