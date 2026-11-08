module

public import Tactics
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Ring.RingNF

/-! Written from tests/elaborator/reading-equations.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingEquations.AnEquationTurnedCarryingAMembership

theorem an_equation_turned_carrying_a_membership (x : ℂ) (r : ℝ) (hH3 : (r : ℂ) = x) :
    (∃ m : ℝ, (m : ℂ) = x) := by
  -- 1. membership, from H3
  exact ⟨r, by first | (push_cast; linarith [hH3]) | (rw [hH3]; push_cast; ring) | (rw [← hH3]; push_cast; ring) | exact hH3 | exact hH3.symm⟩

end Parley.Tests.Elaborator.ReadingEquations.AnEquationTurnedCarryingAMembership
