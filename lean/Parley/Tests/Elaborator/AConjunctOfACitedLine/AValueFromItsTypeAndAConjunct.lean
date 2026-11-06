module

public import AlgebraTactics
public import SetTactics
public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Order.Interval.Set.Defs
public import Parley.Items.Stdlib.Sets

/-! Written from tests/elaborator/a-conjunct-of-a-cited-line.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AConjunctOfACitedLine.AValueFromItsTypeAndAConjunct

theorem a_value_from_its_type_and_a_conjunct (a : ℝ) (b : ℝ) (c : ℝ) (hH3 : c ∈ (Set.Ioo a b : Set ℝ)) (h : ℝ → ℝ) (hH4 : Set.MapsTo h (Set.Ioo a b : Set ℝ) (Set.univ : Set ℝ)) (x : ℝ) (hH5 : x ∈ (Set.Ioo a b : Set ℝ) \ ({c} : Set ℝ)) :
    h x + 1 = 1 + h x := by
  -- 1. mun:remove-member, from H5
  have s1 : x ∈ (Set.Ioo a b : Set ℝ) ∧ x ≠ c := by first | exact ((Parley.Items.Stdlib.Sets.mun_remove_member (Y := (Set.Ioo a b : Set ℝ)) (a := c) (u := x))).mp (by parley_set_side) | exact (((Parley.Items.Stdlib.Sets.mun_remove_member (Y := (Set.Ioo a b : Set ℝ)) (a := c) (u := x))).mp (by parley_set_side)).symm | simpa using ((Parley.Items.Stdlib.Sets.mun_remove_member (Y := (Set.Ioo a b : Set ℝ)) (a := c) (u := x))).mp (by parley_set_side) | exact_mod_cast ((Parley.Items.Stdlib.Sets.mun_remove_member (Y := (Set.Ioo a b : Set ℝ)) (a := c) (u := x))).mp (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.mun_remove_member (Y := (Set.Ioo a b : Set ℝ)) (a := c) (u := x))).mp (by parley_set_side); parley_set_side)
  -- 2. algebra
  have s2 : h x + 1 = 1 + h x := by parley_ring
  all_goals exact s2

end Parley.Tests.Elaborator.AConjunctOfACitedLine.AValueFromItsTypeAndAConjunct
