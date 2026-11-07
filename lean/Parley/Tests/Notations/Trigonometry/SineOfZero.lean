module

public import Tactics
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Parley.Items.Stdlib.Trigonometry

/-! Written from tests/notations/trigonometry.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Trigonometry.SineOfZero

theorem sine_of_zero :
    Real.sin (0 : ℝ) = 0 := by
  -- 1. mun:sin-zero
  have s1 : Real.sin (0 : ℝ) = 0 := by exact Parley.Items.Stdlib.Trigonometry.mun_sin_zero
  all_goals exact s1

end Parley.Tests.Notations.Trigonometry.SineOfZero
