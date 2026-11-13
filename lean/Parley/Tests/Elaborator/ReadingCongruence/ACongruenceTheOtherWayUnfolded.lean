module

public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Divisibility

/-! Written from tests/elaborator/reading-congruence.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingCongruence.ACongruenceTheOtherWayUnfolded

theorem a_congruence_the_other_way_unfolded (a : ℤ) (b : ℤ) (n : ℤ) (hH3 : 0 < n) (hH4 : b ≡ a [ZMOD n]) :
    n ∣ a - b := by
  -- 1. def:congruent-mod, from H4
  exact ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := n) (a := a) (b := b))).mp hH4.symm

end Parley.Tests.Elaborator.ReadingCongruence.ACongruenceTheOtherWayUnfolded
