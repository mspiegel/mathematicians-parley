module

public import NormTactics
public import PowerTactics
public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify

/-! Written from tests/elaborator/reading-equations.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingEquations.AnEquationTurnedInAnInstantiate

theorem an_equation_turned_in_an_instantiate (y : ℝ) (hH2 : ∀ x : ℝ, x = x * 1) :
    y * 1 = y := by
  -- 1. instantiate x := y in H2
  first | linear_combination (norm := parley_norm) (hH2 y) | (have h := (hH2 y); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (hH2 y); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (hH2 y) | exact_mod_cast ((hH2 y)).symm | (have h := (hH2 y); rify; linear_combination (norm := parley_norm) h) | (have h := (hH2 y); qify; linear_combination (norm := parley_norm) h) | (have h := (hH2 y); parley_int_power h) | (have h := (hH2 y); parley_side)

end Parley.Tests.Elaborator.ReadingEquations.AnEquationTurnedInAnInstantiate
