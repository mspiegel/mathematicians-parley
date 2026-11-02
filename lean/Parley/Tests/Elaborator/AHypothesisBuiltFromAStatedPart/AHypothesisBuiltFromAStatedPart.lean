module

public import LeanBridges
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/elaborator/a-hypothesis-built-from-a-stated-part.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AHypothesisBuiltFromAStatedPart.AHypothesisBuiltFromAStatedPart

theorem a_hypothesis_built_from_a_stated_part (n : ℕ) (hH1 : 0 < n) (f : ℤ → ℝ) :
    (f (n : ℤ) + 1) ^ 2 ≥ 0 := by
  -- 1. mun:square-nonneg x := f(n) + 1
  have s1 : (f (n : ℤ) + 1) ^ 2 ≥ 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := f (n : ℤ) + 1))] | (have h := (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := f (n : ℤ) + 1)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := f (n : ℤ) + 1))
  all_goals parley_side

end Parley.Tests.Elaborator.AHypothesisBuiltFromAStatedPart.AHypothesisBuiltFromAStatedPart
