module

public import RealTactics
public import Tactics
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Logarithms
public import Parley.Items.Stdlib.Numbers
public import Parley.Proofs.Hammack.LogThreeOverTwoIrrational.PowerOfThreeOdd
public import Parley.Proofs.Hammack.LogThreeOverTwoIrrational.PowerOfTwoEven

/-! Written from proofs/hammack/log-three-over-two-irrational.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.LogThreeOverTwoIrrational.LogThreeOverTwoIrrational

theorem log_three_over_two_irrational :
    Irrational (Real.log (3 : ℝ) / Real.log (2 : ℝ)) := by
  -- 1. mun:quotient-positive x := ln(3), y := ln(2)
  have r90_1 : Real.log (3 : ℝ) > 0 := by parley_real
  have r90_2 : Real.log (2 : ℝ) > 0 := by parley_real
  have s1 : Real.log (3 : ℝ) / Real.log (2 : ℝ) > 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_quotient_positive (x := Real.log (3 : ℝ)) (y := Real.log (2 : ℝ)) (by parley_side) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_quotient_positive (x := Real.log (3 : ℝ)) (y := Real.log (2 : ℝ)) (by parley_side) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_quotient_positive (x := Real.log (3 : ℝ)) (y := Real.log (2 : ℝ)) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_quotient_positive (x := Real.log (3 : ℝ)) (y := Real.log (2 : ℝ)) (by parley_side) (by parley_side)); parley_side)
  -- 2. contradiction
  have s2 : ¬ (∃ m : ℚ, (m : ℝ) = Real.log (3 : ℝ) / Real.log (2 : ℝ)) := by
    by_contra hc_hS
    have hS : ∃ m : ℚ, (m : ℝ) = Real.log (3 : ℝ) / Real.log (2 : ℝ) := by parley_suppose hc_hS
    -- 2.1. obtain p, q: def:rational x := ln(3)/ln(2), from S
    obtain ⟨p, q, s2_1a, s2_1b⟩ := ((Parley.Items.Stdlib.Numbers.def_rational (x := Real.log (3 : ℝ) / Real.log (2 : ℝ)))).mp (by parley_side)
    -- 2.2. mun:product-positive x := ln(3)/ln(2), y := q, from 1, 2.1
    have r102_1 : Real.log (2 : ℝ) ≠ 0 := by parley_real
    have s2_2 : Real.log (3 : ℝ) / Real.log (2 : ℝ) * (q : ℝ) > 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_product_positive (x := Real.log (3 : ℝ) / Real.log (2 : ℝ)) (y := (q : ℝ)) (by parley_side) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_product_positive (x := Real.log (3 : ℝ) / Real.log (2 : ℝ)) (y := (q : ℝ)) (by parley_side) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_product_positive (x := Real.log (3 : ℝ) / Real.log (2 : ℝ)) (y := (q : ℝ)) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_product_positive (x := Real.log (3 : ℝ) / Real.log (2 : ℝ)) (y := (q : ℝ)) (by parley_side) (by parley_side)); parley_side)
    -- 2.3. substitute
    have r106_1 : Real.log (2 : ℝ) ≠ 0 := by parley_real
    have s2_3 : p > 0 := by
      have c1 : Real.log (3 : ℝ) / Real.log (2 : ℝ) * (q : ℝ) = (p : ℝ) := by linear_combination (norm := parley_field) ((q : ℝ)) * s2_1b
      have row1 : p > 0 := by parley_subst_at c1 s2_2
      exact row1
    -- 2.4. mun:pos-int-nat m := p, from 2.3
    have s2_4 : 0 < p := by first | exact (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := p) (by parley_side)) | exact ((Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := p) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := p) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := p) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := p) (by parley_side)); parley_side)
    lift p to ℕ using s2_4.le
    -- 2.5. calculation
    have r115_1 : (3 : ℤ) > 0 := by parley_arith
    have r115_2 : (2 : ℤ) > 0 := by parley_arith
    have r115_3 : Real.log (2 : ℝ) ≠ 0 := by parley_real
    have s2_5 : Real.log (3 ^ q : ℝ) = Real.log (2 ^ p : ℝ) := by
      calc Real.log (3 ^ q : ℝ) = (q : ℝ) * Real.log (3 : ℝ) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Logarithms.mun_ln_power (x := (3 : ℝ)) (n := (q : ℤ)) (by parley_side)) | (have h := (Parley.Items.Stdlib.Logarithms.mun_ln_power (x := (3 : ℝ)) (n := (q : ℤ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Logarithms.mun_ln_power (x := (3 : ℝ)) (n := (q : ℤ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Logarithms.mun_ln_power (x := (3 : ℝ)) (n := (q : ℤ)) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Logarithms.mun_ln_power (x := (3 : ℝ)) (n := (q : ℤ)) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Logarithms.mun_ln_power (x := (3 : ℝ)) (n := (q : ℤ)) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Logarithms.mun_ln_power (x := (3 : ℝ)) (n := (q : ℤ)) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Logarithms.mun_ln_power (x := (3 : ℝ)) (n := (q : ℤ)) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Logarithms.mun_ln_power (x := (3 : ℝ)) (n := (q : ℤ)) (by parley_side)); parley_side)
        _ = (p : ℝ) * Real.log (2 : ℝ) := by linear_combination (norm := parley_field) (Real.log (2 : ℝ) * (q : ℝ)) * s2_1b
        _ = Real.log (2 ^ p : ℝ) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Logarithms.mun_ln_power (x := (2 : ℝ)) (n := (p : ℤ)) (by parley_side)) | (have h := (Parley.Items.Stdlib.Logarithms.mun_ln_power (x := (2 : ℝ)) (n := (p : ℤ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Logarithms.mun_ln_power (x := (2 : ℝ)) (n := (p : ℤ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Logarithms.mun_ln_power (x := (2 : ℝ)) (n := (p : ℤ)) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Logarithms.mun_ln_power (x := (2 : ℝ)) (n := (p : ℤ)) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Logarithms.mun_ln_power (x := (2 : ℝ)) (n := (p : ℤ)) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Logarithms.mun_ln_power (x := (2 : ℝ)) (n := (p : ℤ)) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Logarithms.mun_ln_power (x := (2 : ℝ)) (n := (p : ℤ)) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Logarithms.mun_ln_power (x := (2 : ℝ)) (n := (p : ℤ)) (by parley_side)); parley_side)
    -- 2.6. mun:power-positive a := 3, m := q
    have r124_1 : (3 : ℤ) > 0 := by parley_arith
    have s2_6 : (3 ^ q : ℤ) > 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_power_positive (a := (3 : ℚ)) (m := (q : ℤ)) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_power_positive (a := (3 : ℚ)) (m := (q : ℤ)) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_power_positive (a := (3 : ℚ)) (m := (q : ℤ)) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_power_positive (a := (3 : ℚ)) (m := (q : ℤ)) (by parley_side)); parley_side)
    -- 2.7. mun:power-positive a := 2, m := p
    have r128_1 : (2 : ℤ) > 0 := by parley_arith
    have s2_7 : (2 ^ p : ℤ) > 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_power_positive (a := (2 : ℚ)) (m := (p : ℤ)) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_power_positive (a := (2 : ℚ)) (m := (p : ℤ)) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_power_positive (a := (2 : ℚ)) (m := (p : ℤ)) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_power_positive (a := (2 : ℚ)) (m := (p : ℤ)) (by parley_side)); parley_side)
    -- 2.8. calculation
    have s2_8 : (3 ^ q : ℤ) = 2 ^ p := by
      rify
      calc (3 ^ q : ℝ) = Real.exp (Real.log (3 ^ q : ℝ)) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Logarithms.mun_exp_ln (x := (3 ^ q : ℝ)) (by parley_side)) | (have h := (Parley.Items.Stdlib.Logarithms.mun_exp_ln (x := (3 ^ q : ℝ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Logarithms.mun_exp_ln (x := (3 ^ q : ℝ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Logarithms.mun_exp_ln (x := (3 ^ q : ℝ)) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Logarithms.mun_exp_ln (x := (3 ^ q : ℝ)) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Logarithms.mun_exp_ln (x := (3 ^ q : ℝ)) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Logarithms.mun_exp_ln (x := (3 ^ q : ℝ)) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Logarithms.mun_exp_ln (x := (3 ^ q : ℝ)) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Logarithms.mun_exp_ln (x := (3 ^ q : ℝ)) (by parley_side)); parley_of_complex h) | (have h := (Parley.Items.Stdlib.Logarithms.mun_exp_ln (x := (3 ^ q : ℝ)) (by parley_side)); parley_side)
        _ = Real.exp (Real.log (2 ^ p : ℝ)) := by parley_subst s2_5
        _ = 2 ^ p := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Logarithms.mun_exp_ln (x := (2 ^ p : ℝ)) (by parley_side)) | (have h := (Parley.Items.Stdlib.Logarithms.mun_exp_ln (x := (2 ^ p : ℝ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Logarithms.mun_exp_ln (x := (2 ^ p : ℝ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Logarithms.mun_exp_ln (x := (2 ^ p : ℝ)) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Logarithms.mun_exp_ln (x := (2 ^ p : ℝ)) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Logarithms.mun_exp_ln (x := (2 ^ p : ℝ)) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Logarithms.mun_exp_ln (x := (2 ^ p : ℝ)) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Logarithms.mun_exp_ln (x := (2 ^ p : ℝ)) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Logarithms.mun_exp_ln (x := (2 ^ p : ℝ)) (by parley_side)); parley_of_complex h) | (have h := (Parley.Items.Stdlib.Logarithms.mun_exp_ln (x := (2 ^ p : ℝ)) (by parley_side)); parley_side)
    -- 2.9. thm:power-of-three-odd n := q
    have s2_9 : Odd (3 ^ q : ℤ) := by first | exact (Parley.Proofs.Hammack.LogThreeOverTwoIrrational.PowerOfThreeOdd.power_of_three_odd (n := q)) | exact ((Parley.Proofs.Hammack.LogThreeOverTwoIrrational.PowerOfThreeOdd.power_of_three_odd (n := q))).symm | simpa using (Parley.Proofs.Hammack.LogThreeOverTwoIrrational.PowerOfThreeOdd.power_of_three_odd (n := q)) | exact_mod_cast (Parley.Proofs.Hammack.LogThreeOverTwoIrrational.PowerOfThreeOdd.power_of_three_odd (n := q)) | (have h := (Parley.Proofs.Hammack.LogThreeOverTwoIrrational.PowerOfThreeOdd.power_of_three_odd (n := q)); parley_side)
    -- 2.10. thm:power-of-two-even n := p, from 2.4
    have s2_10 : Even (2 ^ p : ℤ) := by first | exact (Parley.Proofs.Hammack.LogThreeOverTwoIrrational.PowerOfTwoEven.power_of_two_even (n := p) (by parley_side)) | exact ((Parley.Proofs.Hammack.LogThreeOverTwoIrrational.PowerOfTwoEven.power_of_two_even (n := p) (by parley_side))).symm | simpa using (Parley.Proofs.Hammack.LogThreeOverTwoIrrational.PowerOfTwoEven.power_of_two_even (n := p) (by parley_side)) | exact_mod_cast (Parley.Proofs.Hammack.LogThreeOverTwoIrrational.PowerOfTwoEven.power_of_two_even (n := p) (by parley_side)) | (have h := (Parley.Proofs.Hammack.LogThreeOverTwoIrrational.PowerOfTwoEven.power_of_two_even (n := p) (by parley_side)); parley_side)
    -- 2.11. substitute 2^p = 3^q (line 2.8) into line 2.10
    have s2_11 : Even (3 ^ q : ℤ) := by parley_subst_at s2_8 s2_10
    -- 2.12. mun:odd-not-even n := 3^q, from 2.9
    have s2_12 : ¬ Even (3 ^ q : ℤ) := by first | exact (Parley.Items.Stdlib.Divisibility.mun_odd_not_even (n := (3 ^ q : ℤ)) s2_9) | exact ((Parley.Items.Stdlib.Divisibility.mun_odd_not_even (n := (3 ^ q : ℤ)) s2_9)).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_odd_not_even (n := (3 ^ q : ℤ)) s2_9) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_odd_not_even (n := (3 ^ q : ℤ)) s2_9) | (have h := (Parley.Items.Stdlib.Divisibility.mun_odd_not_even (n := (3 ^ q : ℤ)) s2_9); parley_side)
    all_goals parley_side
  -- 3. mun:quotient-real x := ln(3), y := ln(2)
  have r150_1 : Real.log (2 : ℝ) ≠ 0 := by parley_real
  -- 4. def:irrational x := ln(3)/ln(2), from 2, 3
  have s4 : Irrational (Real.log (3 : ℝ) / Real.log (2 : ℝ)) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Numbers.def_irrational (x := Real.log (3 : ℝ) / Real.log (2 : ℝ)))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Numbers.def_irrational (x := Real.log (3 : ℝ) / Real.log (2 : ℝ)))).mpr (by parley_side); parley_side)
  all_goals exact s4

end Parley.Proofs.Hammack.LogThreeOverTwoIrrational.LogThreeOverTwoIrrational
