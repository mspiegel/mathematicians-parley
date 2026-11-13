module

public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
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
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Trigonometry

/-! Written from tests/stdlib/trigonometry.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Trigonometry.ArctanValues

theorem arctan_values :
    Real.arctan (0 : ℝ) = 0 ∧ Real.arctan (1 : ℝ) = Real.pi / 4 := by
  -- 1. mun:trigonometry-arctan-values
  have s1a : Real.arctan (0 : ℝ) = 0 := by exact Parley.Items.Stdlib.Trigonometry.mun_arctan_values_1
  have s1b : Real.arctan (1 : ℝ) = Real.pi / 4 := by exact Parley.Items.Stdlib.Trigonometry.mun_arctan_values_2
  exact ⟨s1a, s1b⟩

end Parley.Tests.Stdlib.Trigonometry.ArctanValues
