module

public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq

/-! Written from tests/elaborator/primes-and-brackets.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.PrimesAndBrackets.BracketedFormula

theorem bracketed_formula (a : ℝ) (hH2 : ∀ x : ℝ, x ≤ a) :
    a ≤ a := by
  -- 1. instantiate x := a in H2
  exact (hH2 a)

end Parley.Tests.Elaborator.PrimesAndBrackets.BracketedFormula
