module

public import Counting
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Rat.Init
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from tests/elaborator/an-identity-a-substitution-makes.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AnIdentityASubstitutionMakes.AnIdentityASubstitutionMakesAtACoefficient

theorem an_identity_a_substitution_makes_at_a_coefficient (N : ℤ) (hH1 : 0 ≤ N) (k : ℤ) (hH3 : (1 ^ k : ℚ) = 1) :
    (LeanBridges.Counting.choose N k : ℚ) * 1 ^ k = (LeanBridges.Counting.choose N k : ℚ) := by
  -- 1. substitute 1^k = 1 (H3)
  (have h := congrArg (fun t : ℚ => (LeanBridges.Counting.choose N k : ℚ) * t) hH3; push_cast [mul_one] at h ⊢; exact_mod_cast h)

end Parley.Tests.Elaborator.AnIdentityASubstitutionMakes.AnIdentityASubstitutionMakesAtACoefficient
