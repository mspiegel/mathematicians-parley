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
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Parley.Items.Stdlib.Trigonometry

/-! Written from tests/stdlib/trigonometry.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Trigonometry.CosPositive

theorem cos_positive (a : ℝ) (hH1 : a ∈ (Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) : Set ℝ)) :
    0 < Real.cos a := by
  -- 1. mun:trigonometry-cos-positive, from H1
  exact (Parley.Items.Stdlib.Trigonometry.mun_cos_positive (a := a) hH1)

end Parley.Tests.Stdlib.Trigonometry.CosPositive
