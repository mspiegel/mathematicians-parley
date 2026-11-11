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

namespace Parley.Tests.Notations.Primes.FloorOfSevenHalves

theorem floor_of_seven_halves :
    ⌊(7 / 2 : ℝ)⌋ = 3 := by
  -- 1. mun:floor-between x := 7/2, k := 3
  have r133_1 : (3 : ℚ) ≤ 7 / 2 := by parley_arith
  have r133_2 : (7 / 2 : ℚ) < 3 + 1 := by parley_arith
  exact ((Parley.Items.Stdlib.Numbers.mun_floor_between (x := (7 / 2 : ℝ)) (k := (3 : ℤ)))).mpr ⟨by parley_side, by parley_side⟩

end Parley.Tests.Notations.Primes.FloorOfSevenHalves
