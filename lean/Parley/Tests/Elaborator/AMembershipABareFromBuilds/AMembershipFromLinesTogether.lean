module

public import Counting
public import FactorialTactics
public import OrderTactics
public import PowerTactics
public import Tactics
public import Parley.Items.Stdlib.Counting

/-! Written from tests/elaborator/a-membership-a-bare-from-builds.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AMembershipABareFromBuilds.AMembershipFromLinesTogether

theorem a_membership_from_lines_together (k : ℤ) (hH2 : 0 ≤ k) (y : ℝ) (hH4 : y ≤ (LeanBridges.Counting.factorial (k + 1) : ℝ)) (hH5 : (LeanBridges.Counting.factorial (k + 1) : ℤ) ≤ 3) :
    y ≤ 3 := by
  -- 1. mun:factorial-nat n := k, from H2
  have s1 : 0 < (LeanBridges.Counting.factorial k : ℤ) := by first | exact (Parley.Items.Stdlib.Counting.mun_factorial_nat (n := k) (by parley_side)) | exact ((Parley.Items.Stdlib.Counting.mun_factorial_nat (n := k) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Counting.mun_factorial_nat (n := k) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Counting.mun_factorial_nat (n := k) (by parley_side)) | (have h := (Parley.Items.Stdlib.Counting.mun_factorial_nat (n := k) (by parley_side)); parley_side)
  -- 2. def:factorial n := k, from H2
  have s2 : (LeanBridges.Counting.factorial (k + 1) : ℤ) = (LeanBridges.Counting.factorial k : ℤ) * (k + 1) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.def_factorial_3 (n := k) (by parley_side)) | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := k) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := k) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Counting.def_factorial_3 (n := k) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Counting.def_factorial_3 (n := k) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := k) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := k) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := k) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := k) (by parley_side)); parley_side)
  -- 3. transitivity, from H4, H5
  have s3 : y ≤ 3 := by parley_order
  all_goals exact s3

end Parley.Tests.Elaborator.AMembershipABareFromBuilds.AMembershipFromLinesTogether
