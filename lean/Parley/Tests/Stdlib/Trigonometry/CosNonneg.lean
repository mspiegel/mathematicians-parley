module

public import SetTactics
public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Parley.Items.Stdlib.Trigonometry

/-! Written from tests/stdlib/trigonometry.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Trigonometry.CosNonneg

theorem cos_nonneg (a : ℝ) (hH1 : a ∈ (Set.Icc (-(Real.pi / 2)) (Real.pi / 2) : Set ℝ)) :
    0 ≤ Real.cos a := by
  -- 1. mun:trigonometry-cos-nonneg, from H1
  have s1 : 0 ≤ Real.cos a := by first | linarith [(Parley.Items.Stdlib.Trigonometry.mun_cos_nonneg (a := a) hH1)] | (have h := (Parley.Items.Stdlib.Trigonometry.mun_cos_nonneg (a := a) hH1); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Trigonometry.mun_cos_nonneg (a := a) hH1) | (have h := (Parley.Items.Stdlib.Trigonometry.mun_cos_nonneg (a := a) hH1); parley_set_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Trigonometry.CosNonneg
