module

public import Tactics
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Rify
public import Parley.Items.Stdlib.Trigonometry

/-! Written from tests/notations/trigonometry.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Trigonometry.CosineOfZeroNotZero

theorem cosine_of_zero_not_zero :
    Real.cos (0 : ℝ) ≠ 0 := by
  -- 1. mun:cos-zero
  have s1 : Real.cos (0 : ℝ) = 1 := by exact Parley.Items.Stdlib.Trigonometry.mun_cos_zero
  -- 2. contradiction
  intro hS
  -- 2.1. calculation
  have s2_1 : (1 : ℝ) = 0 := by
    try rify
    calc (1 : ℝ) = Real.cos (0 : ℝ) := by exact s1.symm
      _ = 0 := by parley_side
  exact absurd s2_1 (by norm_num)

end Parley.Tests.Notations.Trigonometry.CosineOfZeroNotZero
