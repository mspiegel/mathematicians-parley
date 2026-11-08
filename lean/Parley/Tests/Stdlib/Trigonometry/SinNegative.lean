module

public import Tactics
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Parley.Items.Stdlib.Trigonometry

/-! Written from tests/stdlib/trigonometry.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Trigonometry.SinNegative

theorem sin_negative (a : ℂ) :
    Complex.sin (-a) = -Complex.sin a := by
  -- 1. mun:trigonometry-sin-negative
  exact (Parley.Items.Stdlib.Trigonometry.mun_sin_negative (a := a))

end Parley.Tests.Stdlib.Trigonometry.SinNegative
