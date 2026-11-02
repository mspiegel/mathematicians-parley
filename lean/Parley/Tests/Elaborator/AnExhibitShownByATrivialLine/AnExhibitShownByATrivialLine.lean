module

public import LeanBridges

/-! Written from tests/elaborator/an-exhibit-shown-by-a-trivial-line.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AnExhibitShownByATrivialLine.AnExhibitShownByATrivialLine

theorem an_exhibit_shown_by_a_trivial_line (p : ℕ) (hH1 : 0 < p) (q : ℕ) (hH2 : 0 < q) :
    (∃ n : ℕ, 0 < n ∧ (p : ℤ) * (q : ℤ) = (p : ℤ) * (n : ℤ)) := by
  -- 1. algebra
  have s1 : (p : ℤ) * (q : ℤ) = (p : ℤ) * (q : ℤ) := by parley_ring
  -- 2. exhibit, from 1
  have s2 : ∃ n : ℕ, 0 < n ∧ (p : ℤ) * (q : ℤ) = (p : ℤ) * (n : ℤ) := ⟨q, by parley_side, by parley_side⟩
  all_goals parley_side

end Parley.Tests.Elaborator.AnExhibitShownByATrivialLine.AnExhibitShownByATrivialLine
