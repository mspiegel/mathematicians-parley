module

public import SetTactics
public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Topology.Defs.Basic
public import Parley.Items.Stdlib.Calculus

/-! Written from tests/stdlib/calculus.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Calculus.OpenButForAPoint

theorem open_but_for_a_point (a : ℝ) (b : ℝ) (c : ℝ) (hH3 : c ∈ (Set.Ioo a b : Set ℝ)) :
    IsOpen ((Set.Ioo a b : Set ℝ) \ ({c} : Set ℝ)) := by
  -- 1. mun:open-without-point U := (a, b), from H3
  have r245_1 : (Set.Ioo a b : Set ℝ) ⊆ (Set.univ : Set ℝ) := by first | exact (Parley.Items.Stdlib.Calculus.mun_open_interval_real (a := a) (b := b)) | exact ((Parley.Items.Stdlib.Calculus.mun_open_interval_real (a := a) (b := b))).symm | simpa using (Parley.Items.Stdlib.Calculus.mun_open_interval_real (a := a) (b := b)) | exact_mod_cast (Parley.Items.Stdlib.Calculus.mun_open_interval_real (a := a) (b := b)) | (have h := (Parley.Items.Stdlib.Calculus.mun_open_interval_real (a := a) (b := b)); parley_set_side)
  have r245_2 : IsOpen (Set.Ioo a b : Set ℝ) := by first | exact (Parley.Items.Stdlib.Calculus.mun_open_interval_open (a := a) (b := b)) | exact ((Parley.Items.Stdlib.Calculus.mun_open_interval_open (a := a) (b := b))).symm | simpa using (Parley.Items.Stdlib.Calculus.mun_open_interval_open (a := a) (b := b)) | exact_mod_cast (Parley.Items.Stdlib.Calculus.mun_open_interval_open (a := a) (b := b)) | (have h := (Parley.Items.Stdlib.Calculus.mun_open_interval_open (a := a) (b := b)); parley_set_side)
  have s1 : IsOpen ((Set.Ioo a b : Set ℝ) \ ({c} : Set ℝ)) := by first | exact (Parley.Items.Stdlib.Calculus.mun_open_without_point (U := (Set.Ioo a b : Set ℝ)) (c := c) (by parley_set_side) (by parley_set_side) hH3) | exact ((Parley.Items.Stdlib.Calculus.mun_open_without_point (U := (Set.Ioo a b : Set ℝ)) (c := c) (by parley_set_side) (by parley_set_side) hH3)).symm | simpa using (Parley.Items.Stdlib.Calculus.mun_open_without_point (U := (Set.Ioo a b : Set ℝ)) (c := c) (by parley_set_side) (by parley_set_side) hH3) | exact_mod_cast (Parley.Items.Stdlib.Calculus.mun_open_without_point (U := (Set.Ioo a b : Set ℝ)) (c := c) (by parley_set_side) (by parley_set_side) hH3) | (have h := (Parley.Items.Stdlib.Calculus.mun_open_without_point (U := (Set.Ioo a b : Set ℝ)) (c := c) (by parley_set_side) (by parley_set_side) hH3); parley_set_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Calculus.OpenButForAPoint
