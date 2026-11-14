module

public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Ring.Basic

/-! Written from tests/elaborator/an-exhibit-shown-by-a-trivial-line.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AnExhibitShownByATrivialLine.AnExhibitShownByATrivialLine

theorem an_exhibit_shown_by_a_trivial_line (p : ℤ) (hH1 : 0 < p) (q : ℤ) (hH2 : 0 < q) :
    (∃ n : ℤ, 0 < n ∧ p * q = p * n) := by
  -- 1. algebra
  have s1 : p * q = p * q := by ring1
  -- 2. exhibit, from 1
  exact ⟨q, hH2, rfl⟩

end Parley.Tests.Elaborator.AnExhibitShownByATrivialLine.AnExhibitShownByATrivialLine
