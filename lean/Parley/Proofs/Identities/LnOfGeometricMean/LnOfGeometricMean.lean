module

public import NormTactics
public import PowerTactics
public import SubstTactics
public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Parley.Items.Stdlib.Logarithms
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/identities/ln-of-geometric-mean.proof by parley build lean. -/

public section

namespace Parley.Proofs.Identities.LnOfGeometricMean.LnOfGeometricMean

theorem ln_of_geometric_mean (x : ℝ) (y : ℝ) (hH3 : x > 0) (hH4 : y > 0) :
    Real.log (Real.sqrt (x * y)) = (Real.log x + Real.log y) / 2 := by
  -- 1. mun:product-positive, from H3, H4
  have s1 : x * y > 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_product_positive (x := x) (y := y) (by parley_side) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_product_positive (x := x) (y := y) (by parley_side) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_product_positive (x := x) (y := y) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_product_positive (x := x) (y := y) (by parley_side) (by parley_side)); parley_side)
  -- 2. def:sqrt x := x·y
  have r21_1 : x * y ≥ 0 := by parley_side
  have s2a : Real.sqrt (x * y) ≥ 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := x * y) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := x * y) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := x * y) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := x * y) (by parley_side)); parley_side)
  have s2b : Real.sqrt (x * y) ^ 2 = x * y := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := x * y) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := x * y) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := x * y) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := x * y) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := x * y) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := x * y) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := x * y) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := x * y) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := x * y) (by parley_side)); parley_side)
  -- 3. substitute
  have s3 : Real.sqrt (x * y) * Real.sqrt (x * y) > 0 := by
    have c1 : x * y = Real.sqrt (x * y) * Real.sqrt (x * y) := by linear_combination (norm := parley_norm) (-1) * s2b
    have row1 : Real.sqrt (x * y) * Real.sqrt (x * y) > 0 := by parley_subst_at c1 s1
    exact row1
  -- 4. mun:factor-positive a := √(x·y), b := √(x·y), from 2, 3
  have s4 : Real.sqrt (x * y) > 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_factor_positive (a := Real.sqrt (x * y)) (b := Real.sqrt (x * y)) (by parley_side) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_factor_positive (a := Real.sqrt (x * y)) (b := Real.sqrt (x * y)) (by parley_side) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_factor_positive (a := Real.sqrt (x * y)) (b := Real.sqrt (x * y)) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_factor_positive (a := Real.sqrt (x * y)) (b := Real.sqrt (x * y)) (by parley_side) (by parley_side)); parley_side)
  -- 5. restate 2
  have s5 : Real.sqrt (x * y) ^ 2 = x * y := by parley_side
  -- 6. calculation
  have s6 : 2 * Real.log (Real.sqrt (x * y)) = Real.log x + Real.log y := by
    calc 2 * Real.log (Real.sqrt (x * y)) = Real.log (Real.sqrt (x * y) ^ 2) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Logarithms.mun_ln_power (x := Real.sqrt (x * y)) (n := (2 : ℤ)) (by parley_side)) | (have h := (Parley.Items.Stdlib.Logarithms.mun_ln_power (x := Real.sqrt (x * y)) (n := (2 : ℤ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Logarithms.mun_ln_power (x := Real.sqrt (x * y)) (n := (2 : ℤ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Logarithms.mun_ln_power (x := Real.sqrt (x * y)) (n := (2 : ℤ)) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Logarithms.mun_ln_power (x := Real.sqrt (x * y)) (n := (2 : ℤ)) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Logarithms.mun_ln_power (x := Real.sqrt (x * y)) (n := (2 : ℤ)) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Logarithms.mun_ln_power (x := Real.sqrt (x * y)) (n := (2 : ℤ)) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Logarithms.mun_ln_power (x := Real.sqrt (x * y)) (n := (2 : ℤ)) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Logarithms.mun_ln_power (x := Real.sqrt (x * y)) (n := (2 : ℤ)) (by parley_side)); parley_side)
      _ = Real.log (x * y) := by parley_subst s5
      _ = Real.log x + Real.log y := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Logarithms.mun_ln_product (x := x) (y := y) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Logarithms.mun_ln_product (x := x) (y := y) (by parley_side) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Logarithms.mun_ln_product (x := x) (y := y) (by parley_side) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Logarithms.mun_ln_product (x := x) (y := y) (by parley_side) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Logarithms.mun_ln_product (x := x) (y := y) (by parley_side) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Logarithms.mun_ln_product (x := x) (y := y) (by parley_side) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Logarithms.mun_ln_product (x := x) (y := y) (by parley_side) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Logarithms.mun_ln_product (x := x) (y := y) (by parley_side) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Logarithms.mun_ln_product (x := x) (y := y) (by parley_side) (by parley_side)); parley_side)
  -- 7. algebra, from 6
  have s7 : Real.log (Real.sqrt (x * y)) = (Real.log x + Real.log y) / 2 := by linear_combination (norm := parley_norm) ((1) / ((2))) * s6
  all_goals exact s7

end Parley.Proofs.Identities.LnOfGeometricMean.LnOfGeometricMean
