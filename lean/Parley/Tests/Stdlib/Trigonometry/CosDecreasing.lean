module

public import SetTactics
public import Tactics
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

namespace Parley.Tests.Stdlib.Trigonometry.CosDecreasing

theorem cos_decreasing (a : ℝ) (hH1 : a ∈ (Set.Icc (0 : ℝ) Real.pi : Set ℝ)) (b : ℝ) (hH2 : b ∈ (Set.Icc (0 : ℝ) Real.pi : Set ℝ)) :
    (a < b ↔ Real.cos b < Real.cos a) := by
  -- 1. mun:trigonometry-cos-decreasing, from H1, H2
  have s1 : a < b ↔ Real.cos b < Real.cos a := by exact (Parley.Items.Stdlib.Trigonometry.mun_cos_decreasing (a := a) (b := b) hH1 hH2)
  all_goals exact s1

end Parley.Tests.Stdlib.Trigonometry.CosDecreasing
