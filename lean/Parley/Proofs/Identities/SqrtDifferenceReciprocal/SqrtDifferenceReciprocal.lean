module

public import AlgebraTactics
public import OrderTactics
public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/identities/sqrt-difference-reciprocal.proof by parley build lean. -/

public section

namespace Parley.Proofs.Identities.SqrtDifferenceReciprocal.SqrtDifferenceReciprocal

theorem sqrt_difference_reciprocal (x : ℝ) (hH2 : x ≥ 0) :
    Real.sqrt (x + 1) - Real.sqrt x = 1 / (Real.sqrt (x + 1) + Real.sqrt x) := by
  -- 1. inequalities, from H2
  have s1 : x + 1 ≥ 0 := by parley_order
  -- 2. def:sqrt x := x + 1, from 1
  have s2a : Real.sqrt (x + 1) ≥ 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := x + 1) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := x + 1) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := x + 1) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := x + 1) (by parley_side)); parley_side)
  have s2b : Real.sqrt (x + 1) ^ 2 = x + 1 := by exact (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := x + 1) (by parley_side))
  -- 3. def:sqrt, from H2
  have s3a : Real.sqrt x ≥ 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := x) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := x) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := x) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := x) (by parley_side)); parley_side)
  have s3b : Real.sqrt x ^ 2 = x := by exact (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := x) (by parley_side))
  -- 4. inequalities
  have s4 : x < x + 1 := by parley_order
  -- 5. calculation
  have s5 : Real.sqrt x ^ 2 < Real.sqrt (x + 1) ^ 2 := by
    calc Real.sqrt x ^ 2 = x := by parley_side
      _ < x + 1 := by parley_side
      _ = Real.sqrt (x + 1) ^ 2 := by parley_side
  -- 6. mun:square-less x := √x, y := √(x + 1), from 2, 3, 5
  have s6 : Real.sqrt x < Real.sqrt (x + 1) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Numbers.mun_square_less (x := Real.sqrt x) (y := Real.sqrt (x + 1)) (by parley_side) (by parley_side))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_square_less (x := Real.sqrt x) (y := Real.sqrt (x + 1)) (by parley_side) (by parley_side))).mpr (by parley_side); parley_side)
  -- 7. transitivity, from 3, 6
  have s7 : Real.sqrt (x + 1) > 0 := by parley_order
  -- 8. inequalities, from 2, 3, 7
  have s8 : Real.sqrt (x + 1) + Real.sqrt x > 0 := by parley_order
  -- 9. inequalities
  have s9 : Real.sqrt (x + 1) + Real.sqrt x ≠ 0 := by parley_side
  -- 10. algebra, from 2, 3, 9
  have s10 : Real.sqrt (x + 1) - Real.sqrt x = 1 / (Real.sqrt (x + 1) + Real.sqrt x) := by linear_combination (norm := parley_field) ((1) / ((Real.sqrt (x + 1) + Real.sqrt x))) * s2b + ((-1) / ((Real.sqrt (x + 1) + Real.sqrt x))) * s3b
  all_goals exact s10

end Parley.Proofs.Identities.SqrtDifferenceReciprocal.SqrtDifferenceReciprocal
