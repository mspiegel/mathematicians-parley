module

public import OrderTactics
public import Tactics
public import Mathlib.Data.Int.Notation

/-! Written from tests/elaborator/a-sum-of-many-lines-by-inequalities.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ASumOfManyLinesByInequalities.ASumOfSevenNaturals

theorem a_sum_of_seven_naturals (a : ℤ) (hH1 : 0 < a) (b : ℤ) (hH2 : 0 < b) (c : ℤ) (hH3 : 0 < c) (d : ℤ) (hH4 : 0 < d) (e : ℤ) (hH5 : 0 < e) (f : ℤ) (hH6 : 0 < f) (g : ℤ) (hH7 : 0 < g) :
    a + b + c + d + e + f + g > 0 := by
  -- 1. inequalities, from H1, H2, H3, H4, H5, H6, H7
  have s1 : a + b + c + d + e + f + g > 0 := by parley_order
  all_goals exact s1

end Parley.Tests.Elaborator.ASumOfManyLinesByInequalities.ASumOfSevenNaturals
