module

public import Tactics
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Parley.Items.Stdlib.Trigonometry

/-! Written from tests/stdlib/trigonometry.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Trigonometry.SinComplex

theorem sin_complex (a : ℂ) :
    True := by
  -- 1. mun:trigonometry-sin-complex
  all_goals parley_side

end Parley.Tests.Stdlib.Trigonometry.SinComplex
