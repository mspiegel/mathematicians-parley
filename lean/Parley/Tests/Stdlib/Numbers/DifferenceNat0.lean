module

public import Tactics
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/stdlib/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Numbers.DifferenceNat0

theorem difference_nat0 (j : ℤ) (hH1 : 0 ≤ j) (k : ℤ) (hH2 : 0 ≤ k) (hH3 : j ≤ k) :
    0 ≤ k - j := by
  -- 1. mun:numbers-difference-nat0 m := j, n := k, from H3
  have s1 : 0 ≤ k - j := by first | exact (Parley.Items.Stdlib.Numbers.mun_difference_nat0 (m := j) (by parley_side) (n := k) (by parley_side) hH3) | exact ((Parley.Items.Stdlib.Numbers.mun_difference_nat0 (m := j) (by parley_side) (n := k) (by parley_side) hH3)).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_difference_nat0 (m := j) (by parley_side) (n := k) (by parley_side) hH3) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_difference_nat0 (m := j) (by parley_side) (n := k) (by parley_side) hH3) | (have h := (Parley.Items.Stdlib.Numbers.mun_difference_nat0 (m := j) (by parley_side) (n := k) (by parley_side) hH3); parley_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Numbers.DifferenceNat0
