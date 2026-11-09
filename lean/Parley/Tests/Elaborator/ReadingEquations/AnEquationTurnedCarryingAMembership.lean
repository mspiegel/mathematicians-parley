module

public import Tactics
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq

/-! Written from tests/elaborator/reading-equations.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingEquations.AnEquationTurnedCarryingAMembership

theorem an_equation_turned_carrying_a_membership (x : ℂ) (r : ℝ) (hH3 : (r : ℂ) = x) :
    (∃ m : ℝ, (m : ℂ) = x) := by
  -- 1. membership, from H3
  exact ⟨r, by exact_mod_cast hH3⟩

end Parley.Tests.Elaborator.ReadingEquations.AnEquationTurnedCarryingAMembership
