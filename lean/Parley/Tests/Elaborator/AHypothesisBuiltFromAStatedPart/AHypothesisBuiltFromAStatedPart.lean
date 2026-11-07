module

public import Tactics
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/elaborator/a-hypothesis-built-from-a-stated-part.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AHypothesisBuiltFromAStatedPart.AHypothesisBuiltFromAStatedPart

theorem a_hypothesis_built_from_a_stated_part (n : ℤ) (hH1 : 0 < n) (f : ℤ → ℝ) :
    (f n + 1) ^ 2 ≥ 0 := by
  -- 1. mun:square-nonneg x := f(n) + 1
  have s1 : (f n + 1) ^ 2 ≥ 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := f n + 1))] | (have h := (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := f n + 1)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := f n + 1)) | (have h := (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := f n + 1)); parley_side)
  all_goals exact s1

end Parley.Tests.Elaborator.AHypothesisBuiltFromAStatedPart.AHypothesisBuiltFromAStatedPart
