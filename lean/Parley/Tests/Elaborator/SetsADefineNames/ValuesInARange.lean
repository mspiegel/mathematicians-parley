module

public import OrderTactics
public import SetTactics
public import Tactics

/-! Written from tests/elaborator/sets-a-define-names.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.SetsADefineNames.ValuesInARange

theorem values_in_a_range (n : ℕ) (hH1 : 0 < n) (m : ℕ) (hH2 : 0 < m) (f : ℤ → ℤ) (hH3 : Set.MapsTo f (Set.Icc (1 : ℤ) (n : ℤ) : Set ℤ) (Set.Icc (1 : ℤ) (m : ℤ) : Set ℤ)) (k : ℤ) (hH4 : k ∈ Finset.Icc (1 : ℤ) (n : ℤ)) :
    f k ≤ f k := by
  -- 1. inequalities
  have s1 : f k ≤ f k := by parley_order
  all_goals exact s1

end Parley.Tests.Elaborator.SetsADefineNames.ValuesInARange
