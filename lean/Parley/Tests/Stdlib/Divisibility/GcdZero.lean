module

public import Tactics
public import Parley.Items.Stdlib.Divisibility

/-! Written from tests/stdlib/divisibility.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Divisibility.GcdZero

theorem gcd_zero (n : ℕ) :
    (Int.gcd (n : ℤ) (0 : ℤ) : ℤ) = (n : ℤ) := by
  -- 1. mun:divisibility-gcd-zero
  have s1 : (Int.gcd (n : ℤ) (0 : ℤ) : ℤ) = (n : ℤ) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Divisibility.mun_gcd_zero (n := n)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_gcd_zero (n := n)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_gcd_zero (n := n)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_gcd_zero (n := n)) | exact_mod_cast ((Parley.Items.Stdlib.Divisibility.mun_gcd_zero (n := n))).symm | (have h := (Parley.Items.Stdlib.Divisibility.mun_gcd_zero (n := n)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_gcd_zero (n := n)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_gcd_zero (n := n)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_gcd_zero (n := n)); parley_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Divisibility.GcdZero
