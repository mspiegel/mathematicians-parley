module

public import SetTactics
public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.Linarith.Frontend
public import Parley.Items.Stdlib.Calculus

/-! Written from tests/notations/calculus.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Calculus.OneBoundsTheUnitInterval

theorem one_bounds_the_unit_interval :
    (∀ s ∈ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ), s ≤ 1) := by
  -- 1. proof
  have s1 : ∀ s ∈ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ), s ≤ 1 := by
    intro s hK1
    -- 1.1. def:interval a := 0, b := 1, x := s, from K1
    have s1_1 : s ≤ 1 := by first | linarith [(((Parley.Items.Stdlib.Calculus.def_interval (x := s) (a := (0 : ℝ)) (b := (1 : ℝ)))).mp (by parley_set_side)).2] | (have h := (((Parley.Items.Stdlib.Calculus.def_interval (x := s) (a := (0 : ℝ)) (b := (1 : ℝ)))).mp (by parley_set_side)).2; push_cast at h; linarith) | exact_mod_cast (((Parley.Items.Stdlib.Calculus.def_interval (x := s) (a := (0 : ℝ)) (b := (1 : ℝ)))).mp (by parley_set_side)).2 | (have h := (((Parley.Items.Stdlib.Calculus.def_interval (x := s) (a := (0 : ℝ)) (b := (1 : ℝ)))).mp (by parley_set_side)).2; parley_set_side)
    all_goals exact s1_1
  -- 2. def:upper-bound u := 1, S := [0, 1], from 1
  have s2 : ∀ s ∈ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ), s ≤ 1 := by parley_set_side
  all_goals exact s2

end Parley.Tests.Notations.Calculus.OneBoundsTheUnitInterval
