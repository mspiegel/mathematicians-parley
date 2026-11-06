module

public import SetTactics
public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.SetNotationForOrder
public import Parley.Items.Stdlib.Calculus

/-! Written from tests/stdlib/calculus.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Calculus.ClosedBetweenTwoInnerPoints

theorem closed_between_two_inner_points (a : ℝ) (b : ℝ) (p : ℝ) (hH3 : p ∈ (Set.Ioo a b : Set ℝ)) (q : ℝ) (hH4 : q ∈ (Set.Ioo a b : Set ℝ)) :
    (Set.Icc p q : Set ℝ) ⊆ (Set.Ioo a b : Set ℝ) := by
  -- 1. mun:closed-within-open, from H3, H4
  have s1 : (Set.Icc p q : Set ℝ) ⊆ (Set.Ioo a b : Set ℝ) := by first | exact (Parley.Items.Stdlib.Calculus.mun_closed_within_open (p := p) (q := q) (a := a) (b := b) hH3 hH4) | exact ((Parley.Items.Stdlib.Calculus.mun_closed_within_open (p := p) (q := q) (a := a) (b := b) hH3 hH4)).symm | simpa using (Parley.Items.Stdlib.Calculus.mun_closed_within_open (p := p) (q := q) (a := a) (b := b) hH3 hH4) | exact_mod_cast (Parley.Items.Stdlib.Calculus.mun_closed_within_open (p := p) (q := q) (a := a) (b := b) hH3 hH4) | (have h := (Parley.Items.Stdlib.Calculus.mun_closed_within_open (p := p) (q := q) (a := a) (b := b) hH3 hH4); parley_set_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Calculus.ClosedBetweenTwoInnerPoints
