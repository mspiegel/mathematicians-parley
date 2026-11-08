module

public import SetTactics
public import Tactics
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/elaborator/an-interval-member-is-cited.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AnIntervalMemberIsCited.AnIntervalWithoutAPoint

theorem an_interval_without_a_point (a : ℝ) (b : ℝ) (c : ℝ) (x : ℝ) (hH4 : x ∈ (Set.Icc a b : Set ℝ) \ ({c} : Set ℝ)) :
    x ^ 2 ≥ 0 := by
  -- 1. mun:square-nonneg
  exact (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := x))

end Parley.Tests.Elaborator.AnIntervalMemberIsCited.AnIntervalWithoutAPoint
