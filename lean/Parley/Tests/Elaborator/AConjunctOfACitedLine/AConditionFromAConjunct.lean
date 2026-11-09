module

public import SetTactics
public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Parley.Items.Stdlib.Sets

/-! Written from tests/elaborator/a-conjunct-of-a-cited-line.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AConjunctOfACitedLine.AConditionFromAConjunct

theorem a_condition_from_a_conjunct (a : ℝ) (b : ℝ) (c : ℝ) (hH3 : c ∈ (Set.Ioo a b : Set ℝ)) (h : ℝ → ℝ) (hH4 : Set.MapsTo h (Set.Ioo a b : Set ℝ) (Set.univ : Set ℝ)) (hH5 : ∀ x ∈ (Set.Ioo a b : Set ℝ), x ≠ c → h x = 0) (y : ℝ) (hH6 : y ∈ (Set.Ioo a b : Set ℝ) \ ({c} : Set ℝ)) :
    h y = 0 := by
  -- 1. mun:remove-member, from H6
  have s1 : y ∈ (Set.Ioo a b : Set ℝ) ∧ y ≠ c := ((Parley.Items.Stdlib.Sets.mun_remove_member (Y := (Set.Ioo a b : Set ℝ)) (a := c) (u := y))).mp hH6
  -- 2. instantiate x := y in H5, from 1
  exact (hH5 y (by parley_set_side) (by parley_set_side))

end Parley.Tests.Elaborator.AConjunctOfACitedLine.AConditionFromAConjunct
