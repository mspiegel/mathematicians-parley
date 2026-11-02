module

public import LeanBridges
public import Parley.Items.Stdlib.Counting

/-! Written from tests/elaborator/a-membership-a-bare-from-builds.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AMembershipABareFromBuilds.AMembershipFromLinesTogether

theorem a_membership_from_lines_together (k : ℤ) (k : ℕ) (y : ℝ) (hH4 : y ≤ (LeanBridges.Counting.factorial ((k : ℤ) + 1) : ℝ)) (hH5 : (LeanBridges.Counting.factorial ((k : ℤ) + 1) : ℤ) ≤ 3) :
    y ≤ 3 := by
  -- 1. mun:factorial-nat n := k, from H2
  have s1 : 0 < (LeanBridges.Counting.factorial (k : ℤ) : ℤ) := by first | exact (Parley.Items.Stdlib.Counting.mun_factorial_nat (n := k)) | exact ((Parley.Items.Stdlib.Counting.mun_factorial_nat (n := k))).symm | simpa using (Parley.Items.Stdlib.Counting.mun_factorial_nat (n := k)) | exact_mod_cast (Parley.Items.Stdlib.Counting.mun_factorial_nat (n := k))
  -- 2. def:factorial n := k, from H2
  have s2 : (LeanBridges.Counting.factorial ((k : ℤ) + 1) : ℤ) = (LeanBridges.Counting.factorial (k : ℤ) : ℤ) * ((k : ℤ) + 1) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.def_factorial_3 (n := k)) | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := k)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | exact_mod_cast (Parley.Items.Stdlib.Counting.def_factorial_3 (n := k)) | exact_mod_cast ((Parley.Items.Stdlib.Counting.def_factorial_3 (n := k))).symm | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := k)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := k)); qify; linear_combination (norm := parley_norm) h)
  -- 3. transitivity, from H4, H5
  have s3 : y ≤ 3 := by parley_side
  all_goals parley_side

end Parley.Tests.Elaborator.AMembershipABareFromBuilds.AMembershipFromLinesTogether
