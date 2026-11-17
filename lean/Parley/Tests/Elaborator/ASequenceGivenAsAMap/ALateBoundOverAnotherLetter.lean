module

public import Batteries.Classes.RatCast
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Rat.Cast.CharZero
public import Mathlib.Data.Rat.Cast.Defs
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Data.Rat.Init
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs
public import Parley.Items.Stdlib.Calculus
public import Parley.Items.Stdlib.Functions

/-! Written from tests/elaborator/a-sequence-given-as-a-map.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ASequenceGivenAsAMap.ALateBoundOverAnotherLetter

theorem a_late_bound_over_another_letter (L : ℝ) (hH2 : Filter.Tendsto (fun n : ℤ => (1 / (n : ℝ) : ℝ)) Filter.atTop (nhds L)) (hH3 : ∀ i : ℤ, 0 < i → i ≥ 1 → 1 / (i : ℚ) ≤ 1) :
    L ≤ 1 := by
  -- 1. thm:limit-at-most x := (n ∈ ℕ ↦ u(n)), B := 1, N := 1, from H2, H3
  exact (Parley.Items.Stdlib.Calculus.thm_limit_at_most (x := (fun x : ℤ => (((fun n : ℤ => 1 / (n : ℚ)) (x : ℤ) : ℚ) : ℝ))) (L := L) (by (have h := hH2; push_cast at h ⊢; exact h)) (B := (1 : ℝ)) (N := (1 : ℤ)) (by norm_num) (by intro n h_n h_3; exact by have h := (Rat.cast_le (K := ℝ)).mpr (hH3 n h_n h_3); simp only [Rat.cast_div, Rat.cast_one, Rat.cast_intCast] at h; push_cast at h ⊢; exact h))

end Parley.Tests.Elaborator.ASequenceGivenAsAMap.ALateBoundOverAnotherLetter
