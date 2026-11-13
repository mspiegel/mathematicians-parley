module

public import AlgebraTactics
public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.Positivity.Basic

/-! Written from tests/elaborator/a-congruence-chain-opening-with-an-equation.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ACongruenceChainOpeningWithAnEquation.ACongruenceChainOpeningWithAnEquation

theorem a_congruence_chain_opening_with_an_equation (a : ℤ) (b : ℤ) (n : ℤ) (hH3 : 0 < n) (f : ℤ → ℝ) (hH5 : ∃ m : ℤ, (m : ℝ) = f a) (hH6 : (Classical.choose hH5 : ℤ) * a ≡ b [ZMOD n]) (hH7 : b ≡ (1 : ℤ) [ZMOD n]) :
    a * (Classical.choose hH5 : ℤ) ≡ (1 : ℤ) [ZMOD n] := by
  -- 1. algebra, from H5
  have s1 : a * (Classical.choose hH5 : ℤ) = (Classical.choose hH5 : ℤ) * a := by parley_ring
  -- 2. calculation
  calc a * (Classical.choose hH5 : ℤ) = (Classical.choose hH5 : ℤ) * a := s1
    _ ≡ b [ZMOD n] := hH6
    _ ≡ 1 [ZMOD n] := hH7

end Parley.Tests.Elaborator.ACongruenceChainOpeningWithAnEquation.ACongruenceChainOpeningWithAnEquation
