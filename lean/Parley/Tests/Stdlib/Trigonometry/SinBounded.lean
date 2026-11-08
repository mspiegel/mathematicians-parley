module

public import Tactics
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Parley.Items.Stdlib.Trigonometry

/-! Written from tests/stdlib/trigonometry.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Trigonometry.SinBounded

theorem sin_bounded (a : ℝ) :
    -1 ≤ Real.sin a ∧ Real.sin a ≤ 1 := by
  -- 1. mun:trigonometry-sin-bounded
  have s1a : -1 ≤ Real.sin a := by exact (Parley.Items.Stdlib.Trigonometry.mun_sin_bounded_1 (a := a))
  have s1b : Real.sin a ≤ 1 := by exact (Parley.Items.Stdlib.Trigonometry.mun_sin_bounded_2 (a := a))
  exact ⟨s1a, s1b⟩

end Parley.Tests.Stdlib.Trigonometry.SinBounded
