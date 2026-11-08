module

public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Parley.Items.Stdlib.Trigonometry

/-! Written from tests/stdlib/trigonometry.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Trigonometry.ArctanReal

theorem arctan_real (y : ℝ) :
    True := by
  -- 1. mun:trigonometry-arctan-real x := y
  exact trivial

end Parley.Tests.Stdlib.Trigonometry.ArctanReal
