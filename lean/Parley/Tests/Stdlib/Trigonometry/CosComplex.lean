module

public import Tactics
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Parley.Items.Stdlib.Trigonometry

/-! Written from tests/stdlib/trigonometry.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Trigonometry.CosComplex

theorem cos_complex (a : ℂ) :
    True := by
  -- 1. mun:trigonometry-cos-complex
  exact trivial

end Parley.Tests.Stdlib.Trigonometry.CosComplex
