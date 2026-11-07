module

public import NormTactics
public import PowerTactics
public import Tactics
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/identities/sqrt-of-square.proof by parley build lean. -/

public section

namespace Parley.Proofs.Identities.SqrtOfSquare.SqrtOfSquare

theorem sqrt_of_square (x : ℝ) :
    Real.sqrt (x ^ 2) = abs x := by
  -- 1. mun:square-nonneg
  have s1 : x ^ 2 ≥ 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := x))] | (have h := (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := x)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := x)) | (have h := (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := x)); parley_side)
  -- 2. def:sqrt x := x², from 1
  have s2a : Real.sqrt (x ^ 2) ≥ 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := x ^ 2) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := x ^ 2) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := x ^ 2) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := x ^ 2) (by parley_side)); parley_side)
  have s2b : Real.sqrt (x ^ 2) ^ 2 = x ^ 2 := by exact (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := x ^ 2) (by parley_side))
  -- 3. mun:abs-nonneg
  have s3 : abs x ≥ 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_abs_nonneg (x := (x : ℂ)))] | (have h := (Parley.Items.Stdlib.Numbers.mun_abs_nonneg (x := (x : ℂ))); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_abs_nonneg (x := (x : ℂ))) | (have h := (Parley.Items.Stdlib.Numbers.mun_abs_nonneg (x := (x : ℂ))); parley_side)
  -- 4. calculation
  have s4 : Real.sqrt (x ^ 2) ^ 2 = abs x ^ 2 := by
    calc Real.sqrt (x ^ 2) ^ 2 = x ^ 2 := by parley_side
      _ = abs x ^ 2 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_abs_square (x := x)) | (have h := (Parley.Items.Stdlib.Numbers.mun_abs_square (x := x)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_abs_square (x := x)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_abs_square (x := x)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_abs_square (x := x))).symm | (have h := (Parley.Items.Stdlib.Numbers.mun_abs_square (x := x)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_abs_square (x := x)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_abs_square (x := x)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.mun_abs_square (x := x)); parley_side)
  -- 5. mun:square-equal x := √(x²), y := |x|, from 2, 3, 4
  have s5 : Real.sqrt (x ^ 2) = abs x := by first | linear_combination (norm := parley_norm) ((Parley.Items.Stdlib.Numbers.mun_square_equal (x := Real.sqrt (x ^ 2)) (y := abs x) (by parley_side) (by parley_side))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_square_equal (x := Real.sqrt (x ^ 2)) (y := abs x) (by parley_side) (by parley_side))).mp (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := ((Parley.Items.Stdlib.Numbers.mun_square_equal (x := Real.sqrt (x ^ 2)) (y := abs x) (by parley_side) (by parley_side))).mp (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_square_equal (x := Real.sqrt (x ^ 2)) (y := abs x) (by parley_side) (by parley_side))).mp (by parley_side) | exact_mod_cast (((Parley.Items.Stdlib.Numbers.mun_square_equal (x := Real.sqrt (x ^ 2)) (y := abs x) (by parley_side) (by parley_side))).mp (by parley_side)).symm | (have h := ((Parley.Items.Stdlib.Numbers.mun_square_equal (x := Real.sqrt (x ^ 2)) (y := abs x) (by parley_side) (by parley_side))).mp (by parley_side); rify; linear_combination (norm := parley_norm) h) | (have h := ((Parley.Items.Stdlib.Numbers.mun_square_equal (x := Real.sqrt (x ^ 2)) (y := abs x) (by parley_side) (by parley_side))).mp (by parley_side); qify; linear_combination (norm := parley_norm) h) | (have h := ((Parley.Items.Stdlib.Numbers.mun_square_equal (x := Real.sqrt (x ^ 2)) (y := abs x) (by parley_side) (by parley_side))).mp (by parley_side); parley_int_power h) | (have h := ((Parley.Items.Stdlib.Numbers.mun_square_equal (x := Real.sqrt (x ^ 2)) (y := abs x) (by parley_side) (by parley_side))).mp (by parley_side); parley_side)
  all_goals exact s5

end Parley.Proofs.Identities.SqrtOfSquare.SqrtOfSquare
