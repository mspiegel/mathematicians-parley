module

public import Tactics
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Rat.Init
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/stdlib/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Numbers.Rational

theorem rational (x : ℚ) :
    (∃ p : ℤ, ∃ q : ℤ, 0 < q ∧ x = (p : ℚ) / (q : ℚ)) := by
  -- 1. def:numbers-rational, from H2
  have s1 : ∃ p : ℤ, ∃ q : ℤ, 0 < q ∧ x = (p : ℚ) / (q : ℚ) := by first | exact ((Parley.Items.Stdlib.Numbers.def_rational (x := x))).mp (by parley_side) | exact (((Parley.Items.Stdlib.Numbers.def_rational (x := x))).mp (by parley_side)).symm | simpa using ((Parley.Items.Stdlib.Numbers.def_rational (x := x))).mp (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.def_rational (x := x))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Numbers.def_rational (x := x))).mp (by parley_side); parley_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Numbers.Rational
