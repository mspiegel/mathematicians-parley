module

public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/elaborator/an-interval-member-is-cited.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AnIntervalMemberIsCited.AnIntervalMemberIsCited

theorem an_interval_member_is_cited (a : ℝ) (b : ℝ) (x : ℝ) (hH3 : x ∈ (Set.Ioo a b : Set ℝ)) :
    x ^ 2 ≥ 0 := by
  -- 1. mun:square-nonneg
  exact (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := x))

end Parley.Tests.Elaborator.AnIntervalMemberIsCited.AnIntervalMemberIsCited
