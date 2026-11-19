module

public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Trigonometry

/-! Written from tests/stdlib/trigonometry.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Trigonometry.SpecialAngles

theorem special_angles :
    Real.cos ((90 : ℝ) * Real.pi / 180) = 0 ∧ Real.sin ((90 : ℝ) * Real.pi / 180) = 1 ∧ Real.cos ((60 : ℝ) * Real.pi / 180) = 1 / 2 ∧ Real.sin ((30 : ℝ) * Real.pi / 180) = 1 / 2 := by
  -- 1. mun:trigonometry-special-angles
  have s1a : Real.cos ((90 : ℝ) * Real.pi / 180) = 0 := by exact Parley.Items.Stdlib.Trigonometry.mun_special_angles_1
  have s1b : Real.sin ((90 : ℝ) * Real.pi / 180) = 1 := by exact Parley.Items.Stdlib.Trigonometry.mun_special_angles_2
  have s1c : Real.cos ((60 : ℝ) * Real.pi / 180) = 1 / 2 := by exact Parley.Items.Stdlib.Trigonometry.mun_special_angles_3
  have s1d : Real.sin ((30 : ℝ) * Real.pi / 180) = 1 / 2 := by exact Parley.Items.Stdlib.Trigonometry.mun_special_angles_4
  exact ⟨s1a, s1b, s1c, s1d⟩

end Parley.Tests.Stdlib.Trigonometry.SpecialAngles
