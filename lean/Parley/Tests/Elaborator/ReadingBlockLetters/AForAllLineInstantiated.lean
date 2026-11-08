module

public import NormTactics
public import PowerTactics
public import RealTactics
public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify

/-! Written from tests/elaborator/reading-block-letters.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingBlockLetters.AForAllLineInstantiated

theorem a_for_all_line_instantiated (hH1 : ∀ x : ℝ, ∀ z : ℝ, x * z = z * x) :
    (∀ y : ℝ, y * 2 = 2 * y) := by
  -- 1. proof
  intro y
  -- 1.1. instantiate z := 2 in H1
  first | linear_combination (norm := parley_norm) (hH1 y (2 : ℝ)) | (have h := (hH1 y (2 : ℝ)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (hH1 y (2 : ℝ)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (hH1 y (2 : ℝ)) | exact_mod_cast ((hH1 y (2 : ℝ))).symm | (have h := (hH1 y (2 : ℝ)); rify; linear_combination (norm := parley_norm) h) | (have h := (hH1 y (2 : ℝ)); qify; linear_combination (norm := parley_norm) h) | (have h := (hH1 y (2 : ℝ)); parley_int_power h) | (have h := (hH1 y (2 : ℝ)); parley_rat_of_real h) | (have h := (hH1 y (2 : ℝ)); parley_side)

end Parley.Tests.Elaborator.ReadingBlockLetters.AForAllLineInstantiated
