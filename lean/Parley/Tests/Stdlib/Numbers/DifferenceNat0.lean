module

public import Tactics
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/stdlib/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Numbers.DifferenceNat0

theorem difference_nat0 (j : ℕ) (k : ℕ) (hH3 : (j : ℤ) ≤ (k : ℤ)) :
    0 ≤ (k : ℤ) - (j : ℤ) := by
  -- 1. mun:numbers-difference-nat0 m := j, n := k, from H3
  have s1 : 0 ≤ (k : ℤ) - (j : ℤ) := by first | exact (Parley.Items.Stdlib.Numbers.mun_difference_nat0 (m := j) (n := k) (by parley_side)) | exact ((Parley.Items.Stdlib.Numbers.mun_difference_nat0 (m := j) (n := k) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_difference_nat0 (m := j) (n := k) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_difference_nat0 (m := j) (n := k) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_difference_nat0 (m := j) (n := k) (by parley_side)); parley_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Numbers.DifferenceNat0
