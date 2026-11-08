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

namespace Parley.Tests.Stdlib.Trigonometry.SinNonneg

theorem sin_nonneg (a : ℝ) (hH1 : a ∈ (Set.Icc (0 : ℝ) Real.pi : Set ℝ)) :
    0 ≤ Real.sin a := by
  -- 1. mun:trigonometry-sin-nonneg, from H1
  exact (Parley.Items.Stdlib.Trigonometry.mun_sin_nonneg (a := a) hH1)

end Parley.Tests.Stdlib.Trigonometry.SinNonneg
