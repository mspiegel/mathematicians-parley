module

public import Tactics
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/elaborator/reading-memberships.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingMemberships.ARangeBoundInARequiresLine

theorem a_range_bound_in_a_requires_line (n : ℤ) (k : ℤ) (hH2 : k ∈ Finset.Icc (1 : ℤ) n) (c : ℝ) (hH4 : c ≥ 0) :
    (k : ℝ) * c ≤ (n : ℝ) * c := by
  -- 1. mun:multiply-le-nonneg, from H4
  have r41_1 : k ≤ n := by parley_side
  have s1 : (k : ℝ) * c ≤ (n : ℝ) * c := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_multiply_le_nonneg (x := (k : ℝ)) (y := (n : ℝ)) (c := c) (by parley_side) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_le_nonneg (x := (k : ℝ)) (y := (n : ℝ)) (c := c) (by parley_side) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_multiply_le_nonneg (x := (k : ℝ)) (y := (n : ℝ)) (c := c) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_le_nonneg (x := (k : ℝ)) (y := (n : ℝ)) (c := c) (by parley_side) (by parley_side)); parley_side)
  all_goals exact s1

end Parley.Tests.Elaborator.ReadingMemberships.ARangeBoundInARequiresLine
