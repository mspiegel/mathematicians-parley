module

public import ArithTactics
public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Rat.Init
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/notations/primes.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Primes.FloorOfMinusHalf

theorem floor_of_minus_half :
    ⌊(-(1 / 2) : ℝ)⌋ = -1 := by
  -- 1. mun:floor-between x := −1/2, k := −1
  have r110_1 : (-1 : ℚ) ≤ -(1 / 2) := by parley_arith
  have r110_2 : (-(1 / 2) : ℚ) < -1 + 1 := by parley_arith
  first | (assumption; done) | exact ((Parley.Items.Stdlib.Numbers.mun_floor_between (x := (-(1 / 2) : ℝ)) (k := (-1 : ℤ)))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_floor_between (x := (-(1 / 2) : ℝ)) (k := (-1 : ℤ)))).mpr (by parley_side); parley_side)

end Parley.Tests.Notations.Primes.FloorOfMinusHalf
