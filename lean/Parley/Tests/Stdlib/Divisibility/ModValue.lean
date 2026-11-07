module

public import Divisibility
public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Rat.Floor
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Divisibility

/-! Written from tests/stdlib/divisibility.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Divisibility.ModValue

theorem mod_value (a : ℝ) (b : ℝ) (hH3 : b > 0) :
    LeanBridges.Divisibility.mod a b = a - b * (⌊a / b⌋ : ℝ) := by
  -- 1. mun:divisibility-mod-value, from H3
  have s1 : LeanBridges.Divisibility.mod a b = a - b * (⌊a / b⌋ : ℝ) := by exact (Parley.Items.Stdlib.Divisibility.mun_mod_value (a := a) (b := b) (by parley_side))
  all_goals exact s1

end Parley.Tests.Stdlib.Divisibility.ModValue
