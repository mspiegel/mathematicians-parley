module

public import Parley.Library

/-! Written from tests/elaborator/a-congruence-chain-opening-with-an-equation.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ACongruenceChainOpeningWithAnEquation.ACongruenceChainOpeningWithAnEquation

theorem a_congruence_chain_opening_with_an_equation (a : ℤ) (b : ℤ) (n : ℕ) (hH3 : 0 < n) (f : ℤ → ℝ) (hH5 : ∃ m : ℤ, (m : ℝ) = f a) (hH6 : ((Classical.choose hH5) * a) ≡ b [ZMOD (n : ℤ)]) (hH7 : b ≡ (1 : ℤ) [ZMOD (n : ℤ)]) :
    (a * (Classical.choose hH5)) ≡ (1 : ℤ) [ZMOD (n : ℤ)] := by
  -- 1. algebra, from H5
  have s1 : a * (Classical.choose hH5) = (Classical.choose hH5) * a := by parley_ring
  -- 2. calculation
  have s2 : (a * (Classical.choose hH5)) ≡ (1 : ℤ) [ZMOD (n : ℤ)] := by
    calc a * (Classical.choose hH5) = (Classical.choose hH5) * a := by parley_side
      _ ≡ b [ZMOD (n : ℤ)] := by parley_side
      _ ≡ 1 [ZMOD (n : ℤ)] := by parley_side
  all_goals parley_side

end Parley.Tests.Elaborator.ACongruenceChainOpeningWithAnEquation.ACongruenceChainOpeningWithAnEquation
