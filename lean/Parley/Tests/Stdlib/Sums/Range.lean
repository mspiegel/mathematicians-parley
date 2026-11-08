module

public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Parley.Items.Stdlib.Sums

/-! Written from tests/stdlib/sums.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Sums.Range

theorem range (n : ℤ) (k : ℝ) (hH3 : ∃ m : ℤ, (m : ℝ) = k ∧ m ∈ Finset.Icc (1 : ℤ) n) :
    ((∃ m : ℤ, 0 < m ∧ (m : ℝ) = k) ∧ k ≤ (n : ℝ)) := by
  -- 1. def:sums-range, from H3
  rw [← (Classical.choose_spec hH3).1]; have := (Classical.choose_spec hH3).2; (first | exact ((Parley.Items.Stdlib.Sums.def_range (k := (Classical.choose hH3)) (n := n))).mp (by parley_side) | exact (((Parley.Items.Stdlib.Sums.def_range (k := (Classical.choose hH3)) (n := n))).mp (by parley_side)).symm | simpa using ((Parley.Items.Stdlib.Sums.def_range (k := (Classical.choose hH3)) (n := n))).mp (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Sums.def_range (k := (Classical.choose hH3)) (n := n))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Sums.def_range (k := (Classical.choose hH3)) (n := n))).mp (by parley_side); parley_side))

end Parley.Tests.Stdlib.Sums.Range
