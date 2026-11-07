module

public import Tactics
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Parley.Items.Stdlib.Trigonometry

/-! Written from tests/notations/trigonometry.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Trigonometry.CosineOfZero

theorem cosine_of_zero :
    Real.cos (0 : ℝ) = 1 := by
  -- 1. mun:cos-zero
  have s1 : Real.cos (0 : ℝ) = 1 := by exact Parley.Items.Stdlib.Trigonometry.mun_cos_zero
  all_goals exact s1

end Parley.Tests.Notations.Trigonometry.CosineOfZero
