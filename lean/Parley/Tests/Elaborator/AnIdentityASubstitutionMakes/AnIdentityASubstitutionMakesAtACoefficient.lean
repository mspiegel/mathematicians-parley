module

public import Counting
public import FactorialTactics
public import SubstTactics
public import Tactics
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Rat.Init
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic

/-! Written from tests/elaborator/an-identity-a-substitution-makes.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AnIdentityASubstitutionMakes.AnIdentityASubstitutionMakesAtACoefficient

theorem an_identity_a_substitution_makes_at_a_coefficient (N : ℤ) (hH1 : 0 ≤ N) (k : ℤ) (hH3 : (1 ^ k : ℚ) = 1) :
    (LeanBridges.Counting.choose N k : ℚ) * 1 ^ k = (LeanBridges.Counting.choose N k : ℚ) := by
  -- 1. substitute 1^k = 1 (H3)
  have s1 : (LeanBridges.Counting.choose N k : ℚ) * 1 ^ k = (LeanBridges.Counting.choose N k : ℚ) := by parley_subst hH3
  all_goals exact s1

end Parley.Tests.Elaborator.AnIdentityASubstitutionMakes.AnIdentityASubstitutionMakesAtACoefficient
