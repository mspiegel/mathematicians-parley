module

public import Parley.Items.Stdlib.Numbers
public import Parley.Library

/-! Written from proofs/setmm/natural-at-most-square.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.NaturalAtMostSquare.NaturalAtMostSquare

theorem natural_at_most_square (n : ℕ) (hH1 : 0 < n) :
    (n : ℤ) ≤ (n : ℤ) ^ 2 := by
  -- 1. inequalities, from H1
  have s1 : 1 ≤ (n : ℤ) := by parley_side
  -- 2. mun:multiply-le x := 1, y := n, c := n, from 1
  have r12_1 : (n : ℤ) > 0 := by parley_side
  have s2 : (n : ℤ) * 1 ≤ (n : ℤ) * (n : ℤ) := by linarith [(Parley.Items.Stdlib.Numbers.mun_multiply_le (x := (1 : ℤ)) (y := (n : ℤ)) (c := (n : ℤ)) (by parley_side) (by parley_side))]
  -- 3. algebra
  have s3 : (n : ℤ) ^ 2 = (n : ℤ) * (n : ℤ) := by ring
  -- 4. transitivity, from 2, 3
  have s4 : (n : ℤ) ≤ (n : ℤ) ^ 2 := by parley_side
  all_goals parley_side

end Parley.Proofs.Setmm.NaturalAtMostSquare.NaturalAtMostSquare
