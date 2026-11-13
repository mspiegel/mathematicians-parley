module

public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from tests/elaborator/a-congruence-read-either-way.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ACongruenceReadEitherWay.ACalculationReadingACongruenceTheOtherWay

theorem a_calculation_reading_a_congruence_the_other_way (a : ℤ) (b : ℤ) (c : ℤ) (n : ℤ) (hH4 : 0 < n) (hH5 : a ≡ b [ZMOD n]) (hH6 : c ≡ b [ZMOD n]) :
    a ≡ c [ZMOD n] := by
  -- 1. calculation
  calc a ≡ b [ZMOD n] := hH5
    _ ≡ c [ZMOD n] := hH6.symm

end Parley.Tests.Elaborator.ACongruenceReadEitherWay.ACalculationReadingACongruenceTheOtherWay
