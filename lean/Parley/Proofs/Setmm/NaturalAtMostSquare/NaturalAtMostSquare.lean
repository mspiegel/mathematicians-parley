module

public import AlgebraTactics
public import OrderTactics
public import Tactics
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/setmm/natural-at-most-square.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.NaturalAtMostSquare.NaturalAtMostSquare

theorem natural_at_most_square (n : ℤ) (hH1 : 0 < n) :
    n ≤ n ^ 2 := by
  -- 1. inequalities, from H1
  have s1 : 1 ≤ n := by parley_order
  -- 2. mun:multiply-le x := 1, y := n, c := n, from 1
  have r12_1 : n > 0 := by parley_order
  have s2 : n * 1 ≤ n * n := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_multiply_le (x := (1 : ℤ)) (y := n) (c := n) (by parley_side) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_le (x := (1 : ℤ)) (y := n) (c := n) (by parley_side) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_multiply_le (x := (1 : ℤ)) (y := n) (c := n) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_le (x := (1 : ℤ)) (y := n) (c := n) (by parley_side) (by parley_side)); parley_side)
  -- 3. algebra
  have s3 : n ^ 2 = n * n := by parley_ring
  -- 4. transitivity, from 2, 3
  have s4 : n ≤ n ^ 2 := by parley_order
  all_goals exact s4

end Parley.Proofs.Setmm.NaturalAtMostSquare.NaturalAtMostSquare
