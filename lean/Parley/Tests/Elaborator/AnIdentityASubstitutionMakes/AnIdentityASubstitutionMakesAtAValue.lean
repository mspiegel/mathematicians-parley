module

public import NormTactics
public import SubstTactics
public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Rat.Init
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic

/-! Written from tests/elaborator/an-identity-a-substitution-makes.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AnIdentityASubstitutionMakes.AnIdentityASubstitutionMakesAtAValue

theorem an_identity_a_substitution_makes_at_a_value (b : ℤ → ℝ) (k : ℤ) (hH3 : (1 ^ k : ℚ) = 1) :
    b 0 * 1 ^ k = b 0 := by
  -- 1. substitute 1^k = 1 (H3)
  have hH3_w : (1 ^ k : ℝ) = 1 := by have h := congrArg (fun x : ℚ => (x : ℝ)) hH3; push_cast at h; linear_combination (norm := parley_norm) h
  first | parley_subst hH3_w | parley_subst hH3

end Parley.Tests.Elaborator.AnIdentityASubstitutionMakes.AnIdentityASubstitutionMakesAtAValue
