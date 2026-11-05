module

public import SetTactics
public import Tactics
public import Parley.Items.Stdlib.Calculus

/-! Written from tests/stdlib/calculus.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Calculus.InsideAnOpenInterval

theorem inside_an_open_interval (a : ℝ) (b : ℝ) (x : ℝ) (hH3 : x ∈ (Set.Ioo a b : Set ℝ)) :
    ((True ∧ a < x) ∧ x < b) := by
  -- 1. def:open-interval, from H3
  have s1 : (True ∧ a < x) ∧ x < b := by first | exact ((Parley.Items.Stdlib.Calculus.def_open_interval (x := x) (a := a) (b := b))).mp (by parley_set_side) | exact (((Parley.Items.Stdlib.Calculus.def_open_interval (x := x) (a := a) (b := b))).mp (by parley_set_side)).symm | simpa using ((Parley.Items.Stdlib.Calculus.def_open_interval (x := x) (a := a) (b := b))).mp (by parley_set_side) | exact_mod_cast ((Parley.Items.Stdlib.Calculus.def_open_interval (x := x) (a := a) (b := b))).mp (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Calculus.def_open_interval (x := x) (a := a) (b := b))).mp (by parley_set_side); parley_set_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Calculus.InsideAnOpenInterval
