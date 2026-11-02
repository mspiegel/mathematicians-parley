module

public import LeanBridges
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/elaborator/reading-memberships.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingMemberships.AMembershipBoundInARequiresLineCitingAnItem

theorem a_membership_bound_in_a_requires_line_citing_an_item (x : ℝ) (hH2 : x ≠ 0) (k : ℕ) (hH3 : 0 < k) :
    (x * (k : ℝ)) ^ 2 > 0 := by
  -- 1. mun:square-positive x := x·k
  have r173_1 : x * (k : ℝ) ≠ 0 := by first | exact (Parley.Items.Stdlib.Numbers.mun_product_nonzero (x := x) (y := (k : ℝ)) (by parley_side) (by parley_side)) | exact ((Parley.Items.Stdlib.Numbers.mun_product_nonzero (x := x) (y := (k : ℝ)) (by parley_side) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_product_nonzero (x := x) (y := (k : ℝ)) (by parley_side) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_product_nonzero (x := x) (y := (k : ℝ)) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_product_nonzero (x := x) (y := (k : ℝ)) (by parley_side) (by parley_side)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Numbers.mun_product_nonzero (x := x) (y := (k : ℝ)) (by parley_side) (by parley_side)); parley_side)
  have s1 : (x * (k : ℝ)) ^ 2 > 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_square_positive (x := x * (k : ℝ)) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_square_positive (x := x * (k : ℝ)) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_square_positive (x := x * (k : ℝ)) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_square_positive (x := x * (k : ℝ)) (by parley_side)); parley_side)
  all_goals parley_side

end Parley.Tests.Elaborator.ReadingMemberships.AMembershipBoundInARequiresLineCitingAnItem
