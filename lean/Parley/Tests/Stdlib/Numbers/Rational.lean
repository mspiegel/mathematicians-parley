module

public import Tactics
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/stdlib/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Numbers.Rational

theorem rational (x : ℝ) (x : ℚ) :
    (∃ p : ℤ, ∃ q : ℕ, 0 < q ∧ x = (p : ℚ) / (q : ℚ)) := by
  -- 1. def:numbers-rational, from H2
  have s1 : ∃ p : ℤ, ∃ q : ℕ, 0 < q ∧ x = (p : ℚ) / (q : ℚ) := by first | exact ((Parley.Items.Stdlib.Numbers.def_rational (x := x))).mp (by parley_side) | exact (((Parley.Items.Stdlib.Numbers.def_rational (x := x))).mp (by parley_side)).symm | simpa using ((Parley.Items.Stdlib.Numbers.def_rational (x := x))).mp (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.def_rational (x := x))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Numbers.def_rational (x := x))).mp (by parley_side); parley_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Numbers.Rational
