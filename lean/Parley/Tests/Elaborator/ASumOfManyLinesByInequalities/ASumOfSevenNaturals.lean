module

public import OrderTactics
public import Tactics

/-! Written from tests/elaborator/a-sum-of-many-lines-by-inequalities.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ASumOfManyLinesByInequalities.ASumOfSevenNaturals

theorem a_sum_of_seven_naturals (a : ℕ) (hH1 : 0 < a) (b : ℕ) (hH2 : 0 < b) (c : ℕ) (hH3 : 0 < c) (d : ℕ) (hH4 : 0 < d) (e : ℕ) (hH5 : 0 < e) (f : ℕ) (hH6 : 0 < f) (g : ℕ) (hH7 : 0 < g) :
    (a : ℤ) + (b : ℤ) + (c : ℤ) + (d : ℤ) + (e : ℤ) + (f : ℤ) + (g : ℤ) > 0 := by
  -- 1. inequalities, from H1, H2, H3, H4, H5, H6, H7
  have s1 : (a : ℤ) + (b : ℤ) + (c : ℤ) + (d : ℤ) + (e : ℤ) + (f : ℤ) + (g : ℤ) > 0 := by parley_order
  all_goals exact s1

end Parley.Tests.Elaborator.ASumOfManyLinesByInequalities.ASumOfSevenNaturals
