module

public import AlgebraTactics
public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic

/-! Written from tests/elaborator/an-exhibit-shown-by-a-trivial-line.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AnExhibitShownByATrivialLine.AnExhibitShownByATrivialLine

theorem an_exhibit_shown_by_a_trivial_line (p : ℤ) (hH1 : 0 < p) (q : ℤ) (hH2 : 0 < q) :
    (∃ n : ℤ, 0 < n ∧ p * q = p * n) := by
  -- 1. algebra
  have s1 : p * q = p * q := by parley_ring
  -- 2. exhibit, from 1
  have s2 : ∃ n : ℤ, 0 < n ∧ p * q = p * n := ⟨q, by parley_side, by parley_side⟩
  all_goals exact s2

end Parley.Tests.Elaborator.AnExhibitShownByATrivialLine.AnExhibitShownByATrivialLine
