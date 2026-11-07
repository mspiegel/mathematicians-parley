module

public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq

/-! Written from tests/elaborator/primes-and-brackets.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.PrimesAndBrackets.BracketedFormula

theorem bracketed_formula (a : ℝ) (hH2 : ∀ x : ℝ, x ≤ a) :
    a ≤ a := by
  -- 1. instantiate x := a in H2
  have s1 : a ≤ a := by first | linarith [(hH2 a)] | (have h := (hH2 a); push_cast at h; linarith) | exact_mod_cast (hH2 a) | (have h := (hH2 a); parley_side)
  all_goals exact s1

end Parley.Tests.Elaborator.PrimesAndBrackets.BracketedFormula
