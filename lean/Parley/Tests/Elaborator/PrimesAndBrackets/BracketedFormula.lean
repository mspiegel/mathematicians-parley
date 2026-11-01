module

public import Parley.Library

/-! Written from tests/elaborator/primes-and-brackets.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.PrimesAndBrackets.BracketedFormula

theorem bracketed_formula (a : ℝ) (H2 : ∀ x : ℝ, x ≤ a) :
    a ≤ a := by
  -- 1. instantiate x := a in H2
  have s1 : a ≤ a := by linarith [(H2 a)]
  all_goals parley_side

end Parley.Tests.Elaborator.PrimesAndBrackets.BracketedFormula
