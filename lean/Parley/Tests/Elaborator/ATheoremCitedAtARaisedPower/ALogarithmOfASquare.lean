module

public import Tactics
public import Parley.Items.Stdlib.Logarithms

/-! Written from tests/elaborator/a-theorem-cited-at-a-raised-power.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ATheoremCitedAtARaisedPower.ALogarithmOfASquare

theorem a_logarithm_of_a_square (s : ℝ) (hH2 : s > 0) :
    Real.log (s ^ 2) = 2 * Real.log s := by
  -- 1. mun:ln-power x := s, n := 2, from H2
  have s1 : Real.log (s ^ 2) = 2 * Real.log s := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Logarithms.mun_ln_power (x := s) (n := (2 : ℤ)) (by parley_side)) | (have h := (Parley.Items.Stdlib.Logarithms.mun_ln_power (x := s) (n := (2 : ℤ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Logarithms.mun_ln_power (x := s) (n := (2 : ℤ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Logarithms.mun_ln_power (x := s) (n := (2 : ℤ)) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Logarithms.mun_ln_power (x := s) (n := (2 : ℤ)) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Logarithms.mun_ln_power (x := s) (n := (2 : ℤ)) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Logarithms.mun_ln_power (x := s) (n := (2 : ℤ)) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Logarithms.mun_ln_power (x := s) (n := (2 : ℤ)) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Logarithms.mun_ln_power (x := s) (n := (2 : ℤ)) (by parley_side)); parley_side)
  all_goals parley_side

end Parley.Tests.Elaborator.ATheoremCitedAtARaisedPower.ALogarithmOfASquare
