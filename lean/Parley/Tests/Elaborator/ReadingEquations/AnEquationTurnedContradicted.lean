module

public import Batteries.Tactic.Init
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from tests/elaborator/reading-equations.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingEquations.AnEquationTurnedContradicted

theorem an_equation_turned_contradicted (a : ℝ) (b : ℝ) (hH3 : b = a) :
    a = b := by
  -- 1. contradiction
  by_contra (hS : a ≠ b)
  -- 1.1. restate S
  have s1_1 : a ≠ b := by exact hS
  exact s1_1 hH3.symm

end Parley.Tests.Elaborator.ReadingEquations.AnEquationTurnedContradicted
