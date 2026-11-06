module

public import ArithTactics
public import SetTactics
public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Parley.Items.Stdlib.Calculus

/-! Written from tests/notations/calculus.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Calculus.OneIsInTheUnitInterval

theorem one_is_in_the_unit_interval :
    (1 : ℝ) ∈ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ) := by
  -- 1. def:interval a := 0, b := 1, x := 1
  have r164_1 : (0 : ℤ) ≤ 1 := by parley_arith
  have r164_2 : (1 : ℤ) ≤ 1 := by parley_arith
  have s1 : (1 : ℝ) ∈ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Calculus.def_interval (x := (1 : ℝ)) (a := (0 : ℝ)) (b := (1 : ℝ)))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Calculus.def_interval (x := (1 : ℝ)) (a := (0 : ℝ)) (b := (1 : ℝ)))).mpr (by parley_set_side); parley_set_side)
  all_goals exact s1

end Parley.Tests.Notations.Calculus.OneIsInTheUnitInterval
