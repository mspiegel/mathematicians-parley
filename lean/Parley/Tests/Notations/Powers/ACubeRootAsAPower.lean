module

public import Numbers
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/notations/powers.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Powers.ACubeRootAsAPower

theorem a_cube_root_as_a_power (x : ℝ) (hH2 : x ≥ 0) :
    LeanBridges.Numbers.root 3 x = x ^ (1 / 3 : ℝ) := by
  -- 1. mun:cube-root-as-power, from H2
  exact (Parley.Items.Stdlib.Numbers.mun_cube_root_as_power (x := x) hH2)

end Parley.Tests.Notations.Powers.ACubeRootAsAPower
