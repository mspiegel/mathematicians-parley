module

public import Tactics
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Parley.Items.Stdlib.Trigonometry

/-! Written from tests/stdlib/trigonometry.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Trigonometry.CosNegative

theorem cos_negative (a : ℂ) :
    Complex.cos (-a) = Complex.cos a := by
  -- 1. mun:trigonometry-cos-negative
  exact (Parley.Items.Stdlib.Trigonometry.mun_cos_negative (a := a))

end Parley.Tests.Stdlib.Trigonometry.CosNegative
