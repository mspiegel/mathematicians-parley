module

public import PowerTactics
public import Tactics
public import Parley.Items.Stdlib.Divisibility

/-! Written from tests/stdlib/divisibility.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Divisibility.GcdZero

theorem gcd_zero (n : ℤ) (hH1 : 0 ≤ n) :
    (Int.gcd n (0 : ℤ) : ℤ) = n := by
  -- 1. mun:divisibility-gcd-zero
  have s1 : (Int.gcd n (0 : ℤ) : ℤ) = n := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Divisibility.mun_gcd_zero (n := n) (by parley_side)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_gcd_zero (n := n) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_gcd_zero (n := n) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_gcd_zero (n := n) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Divisibility.mun_gcd_zero (n := n) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Divisibility.mun_gcd_zero (n := n) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_gcd_zero (n := n) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_gcd_zero (n := n) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_gcd_zero (n := n) (by parley_side)); parley_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Divisibility.GcdZero
