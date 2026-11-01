module

public import Parley.Library

/-! Written from tests/elaborator/a-sum-of-many-lines-by-inequalities.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ASumOfManyLinesByInequalities.ASumOfSevenNaturals

theorem a_sum_of_seven_naturals (a : ℕ) (H1 : 0 < a) (b : ℕ) (H2 : 0 < b) (c : ℕ) (H3 : 0 < c) (d : ℕ) (H4 : 0 < d) (e : ℕ) (H5 : 0 < e) (f : ℕ) (H6 : 0 < f) (g : ℕ) (H7 : 0 < g) :
    (a : ℤ) + (b : ℤ) + (c : ℤ) + (d : ℤ) + (e : ℤ) + (f : ℤ) + (g : ℤ) > 0 := by
  -- 1. inequalities, from H1, H2, H3, H4, H5, H6, H7
  have s1 : (a : ℤ) + (b : ℤ) + (c : ℤ) + (d : ℤ) + (e : ℤ) + (f : ℤ) + (g : ℤ) > 0 := by parley_side
  all_goals parley_side

end Parley.Tests.Elaborator.ASumOfManyLinesByInequalities.ASumOfSevenNaturals
