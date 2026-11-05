module

public import PowerTactics
public import Tactics
public import Parley.Items.Stdlib.Divisibility

/-! Written from tests/stdlib/divisibility.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Divisibility.LcmTimesGcd

theorem lcm_times_gcd (a : ℤ) (b : ℤ) :
    (Int.lcm a b : ℤ) * (Int.gcd a b : ℤ) = abs (a * b) := by
  -- 1. mun:divisibility-lcm-times-gcd
  have s1 : (Int.lcm a b : ℤ) * (Int.gcd a b : ℤ) = abs (a * b) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Divisibility.mun_lcm_times_gcd (a := a) (b := b)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_lcm_times_gcd (a := a) (b := b)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_lcm_times_gcd (a := a) (b := b)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_lcm_times_gcd (a := a) (b := b)) | exact_mod_cast ((Parley.Items.Stdlib.Divisibility.mun_lcm_times_gcd (a := a) (b := b))).symm | (have h := (Parley.Items.Stdlib.Divisibility.mun_lcm_times_gcd (a := a) (b := b)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_lcm_times_gcd (a := a) (b := b)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_lcm_times_gcd (a := a) (b := b)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_lcm_times_gcd (a := a) (b := b)); parley_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Divisibility.LcmTimesGcd
