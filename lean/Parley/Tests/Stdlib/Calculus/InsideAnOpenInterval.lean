module

public import SetTactics
public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Parley.Items.Stdlib.Calculus

/-! Written from tests/stdlib/calculus.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Calculus.InsideAnOpenInterval

theorem inside_an_open_interval (a : ℝ) (b : ℝ) (x : ℝ) (hH3 : x ∈ (Set.Ioo a b : Set ℝ)) :
    ((True ∧ a < x) ∧ x < b) := by
  -- 1. def:open-interval, from H3
  have s1 : (True ∧ a < x) ∧ x < b := ((Parley.Items.Stdlib.Calculus.def_open_interval (x := x) (a := a) (b := b))).mp hH3
  exact ⟨⟨trivial, ((s1).1).2⟩, (s1).2⟩

end Parley.Tests.Stdlib.Calculus.InsideAnOpenInterval
