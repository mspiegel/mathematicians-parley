module

public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic

/-! Written from tests/elaborator/algebra-and-inequalities-at-a-member.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AlgebraAndInequalitiesAtAMember.InequalitiesAtAMember

theorem inequalities_at_a_member :
    (∀ i : ℤ, 0 < i → i + 1 > 1) := by
  -- 1. inequalities
  intro i h_i; linarith only [h_i]

end Parley.Tests.Elaborator.AlgebraAndInequalitiesAtAMember.InequalitiesAtAMember
