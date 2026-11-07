module

public import NormTactics
public import PowerTactics
public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify

/-! Written from tests/elaborator/an-instance-without-its-zero.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AnInstanceWithoutItsZero.AnInstanceWithoutItsZero

theorem an_instance_without_its_zero (a : ℤ → ℝ) (hH2 : ∀ k : ℤ, 0 ≤ k → a (k + 1) = a k + 2) :
    a 1 = a 0 + 2 := by
  -- 1. instantiate k := 0 in H2
  have s1 : a 1 = a 0 + 2 := by first | linear_combination (norm := parley_norm) (hH2 (0 : ℤ) (by parley_side)) | (have h := (hH2 (0 : ℤ) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (hH2 (0 : ℤ) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (hH2 (0 : ℤ) (by parley_side)) | exact_mod_cast ((hH2 (0 : ℤ) (by parley_side))).symm | (have h := (hH2 (0 : ℤ) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (hH2 (0 : ℤ) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (hH2 (0 : ℤ) (by parley_side)); parley_int_power h) | (have h := (hH2 (0 : ℤ) (by parley_side)); parley_side)
  all_goals exact s1

end Parley.Tests.Elaborator.AnInstanceWithoutItsZero.AnInstanceWithoutItsZero
