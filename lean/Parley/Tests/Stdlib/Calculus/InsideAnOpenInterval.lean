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
public import Parley.Items.Stdlib.Calculus

/-! Written from tests/stdlib/calculus.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Calculus.InsideAnOpenInterval

theorem inside_an_open_interval (a : ℝ) (b : ℝ) (x : ℝ) (hH3 : x ∈ (Set.Ioo a b : Set ℝ)) :
    ((True ∧ a < x) ∧ x < b) := by
  -- 1. def:open-interval, from H3
  have s1 : (True ∧ a < x) ∧ x < b := by exact ((Parley.Items.Stdlib.Calculus.def_open_interval (x := x) (a := a) (b := b))).mp hH3
  exact ⟨⟨trivial, ((s1).1).2⟩, (s1).2⟩

end Parley.Tests.Stdlib.Calculus.InsideAnOpenInterval
