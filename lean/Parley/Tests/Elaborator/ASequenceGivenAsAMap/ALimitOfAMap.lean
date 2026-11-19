module

public import Batteries.Classes.RatCast
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
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
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs
public import Parley.Items.Stdlib.Calculus
public import Parley.Items.Stdlib.Functions

/-! Written from tests/elaborator/a-sequence-given-as-a-map.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ASequenceGivenAsAMap.ALimitOfAMap

theorem a_limit_of_a_map (hH1 : ∀ n : ℤ, 0 < n → 1 / (n : ℚ) ≤ 1 / ((n : ℚ) + 1)) (hH2 : ∀ n : ℤ, 0 < n → 1 / (n : ℚ) ≤ 1) :
    (∃ L : ℝ, Filter.Tendsto (fun n : ℤ => (1 / (n : ℝ) : ℝ)) Filter.atTop (nhds L)) := by
  -- 1. obtain L: thm:monotone-limit x := (n ∈ ℕ ↦ u(n)), B := 1, from H1, H2
  obtain ⟨L, s1_obtained⟩ := (Parley.Items.Stdlib.Calculus.thm_monotone_limit (x := (fun x : ℤ => (((fun n : ℤ => 1 / (n : ℚ)) (x : ℤ) : ℚ) : ℝ))) (by intro n h_n; exact by have h := (Rat.cast_le (K := ℝ)).mpr (hH1 n h_n); simp only [Rat.cast_add, Rat.cast_div, Rat.cast_one, Rat.cast_intCast] at h; push_cast at h ⊢; exact h) (B := (1 : ℝ)) (by intro n h_n; exact by have h := (Rat.cast_le (K := ℝ)).mpr (hH2 n h_n); simp only [Rat.cast_div, Rat.cast_one, Rat.cast_intCast] at h; push_cast at h ⊢; exact h))
  have s1 : Filter.Tendsto (fun n : ℤ => (1 / (n : ℝ) : ℝ)) Filter.atTop (nhds L) := by (have h := s1_obtained; push_cast at h ⊢; exact h)
  -- 2. exhibit, from 1
  exact ⟨L, s1⟩

end Parley.Tests.Elaborator.ASequenceGivenAsAMap.ALimitOfAMap
