module

public import Tactics
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.ModEq

/-! Written from tests/elaborator/a-for-all-line-read-in-a-block.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AForAllLineReadInABlock.AForAllLineInACalculationLink

theorem a_for_all_line_in_a_calculation_link (n : ℤ) (hH1 : 0 < n) (c : ℤ) (hH3 : c ≡ (1 : ℤ) [ZMOD n]) (hH4 : ∀ x : ℤ, x ≡ c [ZMOD n]) :
    (∀ b : ℤ, b ≡ (1 : ℤ) [ZMOD n]) := by
  -- 1. proof
  intro b
  -- 1.1. calculation
  calc b ≡ c [ZMOD n] := (hH4 b)
    _ ≡ 1 [ZMOD n] := hH3

end Parley.Tests.Elaborator.AForAllLineReadInABlock.AForAllLineInACalculationLink
