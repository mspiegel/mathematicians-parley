module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.SetNotationForOrder
public import Parley.Items.Stdlib.Calculus

/-! Written from tests/stdlib/calculus.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Calculus.ClosedBetweenTwoInnerPoints

theorem closed_between_two_inner_points (a : ℝ) (b : ℝ) (p : ℝ) (hH3 : p ∈ (Set.Ioo a b : Set ℝ)) (q : ℝ) (hH4 : q ∈ (Set.Ioo a b : Set ℝ)) :
    (Set.Icc p q : Set ℝ) ⊆ (Set.Ioo a b : Set ℝ) := by
  -- 1. mun:closed-within-open, from H3, H4
  exact (Parley.Items.Stdlib.Calculus.mun_closed_within_open (p := p) (q := q) (a := a) (b := b) hH3 hH4)

end Parley.Tests.Stdlib.Calculus.ClosedBetweenTwoInnerPoints
