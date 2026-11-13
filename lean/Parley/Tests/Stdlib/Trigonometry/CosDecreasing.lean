module

public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Trigonometry

/-! Written from tests/stdlib/trigonometry.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Trigonometry.CosDecreasing

theorem cos_decreasing (a : ℝ) (hH1 : a ∈ (Set.Icc (0 : ℝ) Real.pi : Set ℝ)) (b : ℝ) (hH2 : b ∈ (Set.Icc (0 : ℝ) Real.pi : Set ℝ)) :
    (a < b ↔ Real.cos b < Real.cos a) := by
  -- 1. mun:trigonometry-cos-decreasing, from H1, H2
  exact (Parley.Items.Stdlib.Trigonometry.mun_cos_decreasing (a := a) (b := b) hH1 hH2)

end Parley.Tests.Stdlib.Trigonometry.CosDecreasing
