module

public import RealTactics
public import Tactics
public import Parley.Items.Stdlib.Logarithms
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/identities/ln-of-power-of-two-below-exponent.proof by parley build lean. -/

public section

namespace Parley.Proofs.Identities.LnOfPowerOfTwoBelowExponent.LnOfPowerOfTwoBelowExponent

theorem ln_of_power_of_two_below_exponent (n : ℕ) (hH1 : 0 < n) :
    Real.log (2 ^ n : ℝ) < (n : ℝ) := by
  -- 1. real arithmetic
  have s1 : Real.log (2 : ℝ) < 1 := by parley_real
  -- 2. inequalities, from H1
  have s2 : (n : ℤ) > 0 := by parley_order
  -- 3. calculation
  have r16_1 : (2 : ℤ) > 0 := by parley_arith
  have s3 : Real.log (2 ^ n : ℝ) < (n : ℝ) := by
    calc Real.log (2 ^ n : ℝ) = (n : ℝ) * Real.log (2 : ℝ) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Logarithms.mun_ln_power (x := (2 : ℝ)) (n := (n : ℤ)) (by parley_side)) | (have h := (Parley.Items.Stdlib.Logarithms.mun_ln_power (x := (2 : ℝ)) (n := (n : ℤ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Logarithms.mun_ln_power (x := (2 : ℝ)) (n := (n : ℤ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Logarithms.mun_ln_power (x := (2 : ℝ)) (n := (n : ℤ)) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Logarithms.mun_ln_power (x := (2 : ℝ)) (n := (n : ℤ)) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Logarithms.mun_ln_power (x := (2 : ℝ)) (n := (n : ℤ)) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Logarithms.mun_ln_power (x := (2 : ℝ)) (n := (n : ℤ)) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Logarithms.mun_ln_power (x := (2 : ℝ)) (n := (n : ℤ)) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Logarithms.mun_ln_power (x := (2 : ℝ)) (n := (n : ℤ)) (by parley_side)); parley_side)
      _ < (n : ℝ) * 1 := by first | linarith [((Parley.Items.Stdlib.Numbers.mun_less_scaled (x := Real.log (2 : ℝ)) (y := (1 : ℝ)) (c := (n : ℝ)) (by parley_side))).mp (by parley_side)] | (have h := ((Parley.Items.Stdlib.Numbers.mun_less_scaled (x := Real.log (2 : ℝ)) (y := (1 : ℝ)) (c := (n : ℝ)) (by parley_side))).mp (by parley_side); push_cast at h; linarith) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_less_scaled (x := Real.log (2 : ℝ)) (y := (1 : ℝ)) (c := (n : ℝ)) (by parley_side))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_less_scaled (x := Real.log (2 : ℝ)) (y := (1 : ℝ)) (c := (n : ℝ)) (by parley_side))).mp (by parley_side); parley_side)
      _ = (n : ℝ) := by parley_ring
  all_goals exact s3

end Parley.Proofs.Identities.LnOfPowerOfTwoBelowExponent.LnOfPowerOfTwoBelowExponent
