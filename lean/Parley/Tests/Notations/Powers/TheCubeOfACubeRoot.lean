module

public import InstanceTactics
public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/notations/powers.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Powers.TheCubeOfACubeRoot

theorem the_cube_of_a_cube_root (x : ℂ) :
    (x ^ (1 / 3 : ℂ)) ^ 3 = x := by
  -- 1. mun:root-power n := 3
  have hI : (x ^ (1 / 3 : ℂ)) ^ 3 = x := by parley_instance ((Parley.Items.Stdlib.Numbers.mun_root_power (x := x) (n := (3 : ℤ)) (by parley_side)))
  exact hI

end Parley.Tests.Notations.Powers.TheCubeOfACubeRoot
