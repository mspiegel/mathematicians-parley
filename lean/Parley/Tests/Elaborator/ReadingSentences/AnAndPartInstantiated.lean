module

public import NormTactics
public import PowerTactics
public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify

/-! Written from tests/elaborator/reading-sentences.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingSentences.AnAndPartInstantiated

theorem an_and_part_instantiated (a : ℝ) (b : ℝ) (hH3 : a = 1 ∧ (∀ x : ℝ, x * 0 = 0)) :
    b * 0 = 0 := by
  -- 1. instantiate x := b in H3
  have s1 : b * 0 = 0 := by first | linear_combination (norm := parley_norm) (hH3.2 b) | (have h := (hH3.2 b); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (hH3.2 b); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (hH3.2 b) | exact_mod_cast ((hH3.2 b)).symm | (have h := (hH3.2 b); rify; linear_combination (norm := parley_norm) h) | (have h := (hH3.2 b); qify; linear_combination (norm := parley_norm) h) | (have h := (hH3.2 b); parley_int_power h) | (have h := (hH3.2 b); parley_side)
  all_goals exact s1

end Parley.Tests.Elaborator.ReadingSentences.AnAndPartInstantiated
