module

public import Divisibility
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Rat.Floor
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/elaborator/mod-on-the-reals.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ModOnTheReals.TheFractionalPart

theorem the_fractional_part (A : ℝ) :
    LeanBridges.Divisibility.mod A (1 : ℝ) = A - (⌊A⌋ : ℝ) := by
  -- 1. mun:mod-value a := A, b := 1
  have r20_1 : (1 : ℤ) > 0 := by norm_num
  (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_value (a := A) (b := (1 : ℝ)) (by norm_num)); simp only [div_one, one_mul] at h ⊢; exact_mod_cast h)

end Parley.Tests.Elaborator.ModOnTheReals.TheFractionalPart
