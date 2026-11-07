module

public import NormTactics
public import PowerTactics
public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Parley.Tests.Elaborator.ACitedHypothesisAnIdentity.SuccessorSum

/-! Written from tests/elaborator/a-cited-hypothesis-an-identity.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ACitedHypothesisAnIdentity.SuccessorAtZero

theorem successor_at_zero :
    (2 * 1 : ℤ) = 2 * 0 + 2 := by
  -- 1. thm:successor-sum i := 0, j := 1
  have s1 : (2 * 1 : ℤ) = 2 * 0 + 2 := by first | linear_combination (norm := parley_norm) (Parley.Tests.Elaborator.ACitedHypothesisAnIdentity.SuccessorSum.successor_sum (i := (0 : ℤ)) (by parley_side) (j := (1 : ℤ)) (by parley_side) (by parley_side)) | (have h := (Parley.Tests.Elaborator.ACitedHypothesisAnIdentity.SuccessorSum.successor_sum (i := (0 : ℤ)) (by parley_side) (j := (1 : ℤ)) (by parley_side) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Tests.Elaborator.ACitedHypothesisAnIdentity.SuccessorSum.successor_sum (i := (0 : ℤ)) (by parley_side) (j := (1 : ℤ)) (by parley_side) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Tests.Elaborator.ACitedHypothesisAnIdentity.SuccessorSum.successor_sum (i := (0 : ℤ)) (by parley_side) (j := (1 : ℤ)) (by parley_side) (by parley_side)) | exact_mod_cast ((Parley.Tests.Elaborator.ACitedHypothesisAnIdentity.SuccessorSum.successor_sum (i := (0 : ℤ)) (by parley_side) (j := (1 : ℤ)) (by parley_side) (by parley_side))).symm | (have h := (Parley.Tests.Elaborator.ACitedHypothesisAnIdentity.SuccessorSum.successor_sum (i := (0 : ℤ)) (by parley_side) (j := (1 : ℤ)) (by parley_side) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Tests.Elaborator.ACitedHypothesisAnIdentity.SuccessorSum.successor_sum (i := (0 : ℤ)) (by parley_side) (j := (1 : ℤ)) (by parley_side) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Tests.Elaborator.ACitedHypothesisAnIdentity.SuccessorSum.successor_sum (i := (0 : ℤ)) (by parley_side) (j := (1 : ℤ)) (by parley_side) (by parley_side)); parley_int_power h) | (have h := (Parley.Tests.Elaborator.ACitedHypothesisAnIdentity.SuccessorSum.successor_sum (i := (0 : ℤ)) (by parley_side) (j := (1 : ℤ)) (by parley_side) (by parley_side)); parley_side)
  all_goals exact s1

end Parley.Tests.Elaborator.ACitedHypothesisAnIdentity.SuccessorAtZero
