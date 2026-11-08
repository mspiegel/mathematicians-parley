module

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
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Parley.Tests.Notations.Primes.FloorOfMinusHalf

/-! Written from tests/notations/primes.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Primes.FloorOfMinusHalfNotZero

theorem floor_of_minus_half_not_zero :
    ⌊(-(1 / 2) : ℝ)⌋ ≠ 0 := by
  -- 1. thm:floor-of-minus-half
  have s1 : ⌊(-(1 / 2) : ℝ)⌋ = -1 := by exact Parley.Tests.Notations.Primes.FloorOfMinusHalf.floor_of_minus_half
  -- 2. contradiction
  intro hS
  -- 2.1. calculation
  have s2_1 : (-1 : ℤ) = 0 := by
    calc (-1 : ℤ) = ⌊(-(1 / 2) : ℝ)⌋ := by parley_side
      _ = 0 := by parley_side
  exact absurd s2_1 (by norm_num)

end Parley.Tests.Notations.Primes.FloorOfMinusHalfNotZero
