module

public import Tactics
public import Batteries.Classes.RatCast
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Rat.Init
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/stdlib/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Numbers.Rational

theorem rational (x : ℝ) (hH2 : ∃ m : ℚ, (m : ℝ) = x) :
    (∃ p : ℤ, ∃ q : ℤ, 0 < q ∧ x = (p : ℝ) / (q : ℝ)) := by
  -- 1. def:numbers-rational, from H2
  exact ((Parley.Items.Stdlib.Numbers.def_rational (x := x))).mp hH2

end Parley.Tests.Stdlib.Numbers.Rational
