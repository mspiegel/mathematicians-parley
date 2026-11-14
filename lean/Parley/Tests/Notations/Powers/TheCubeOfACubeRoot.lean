module

public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/notations/powers.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Powers.TheCubeOfACubeRoot

theorem the_cube_of_a_cube_root (x : ℂ) :
    (x ^ (1 / 3 : ℂ)) ^ 3 = x := by
  -- 1. mun:root-power n := 3
  have hI : (x ^ (1 / 3 : ℂ)) ^ 3 = x := by (have h := ((Parley.Items.Stdlib.Numbers.mun_root_power (x := x) (n := (3 : ℤ)) (by norm_num))); push_cast at h ⊢; exact h)
  exact hI

end Parley.Tests.Notations.Powers.TheCubeOfACubeRoot
