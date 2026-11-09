module

public import ArithTactics
public import OrderTactics
public import RealTactics
public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.Ring.Unbundled.Rat
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Rat.Defs
public import Mathlib.Data.Rat.Init
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Order.Filter.Defs
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs
public import Parley.Items.Stdlib.Calculus
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/notations/calculus.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Calculus.OneOverNDoesNotTendToOne

set_option maxHeartbeats 400000 in
theorem one_over_n_does_not_tend_to_one :
    ¬ Filter.Tendsto (fun n : ℤ => (1 / (n : ℝ) : ℝ)) Filter.atTop (nhds 1) := by
  -- 1. proof
  -- what this block shows, Lean's types give
  -- 2. contradiction
  intro hS
  -- 2.1. def:tends-to L := 1, from S, 1
  have s2_1 : ∀ ε : ℝ, ε > 0 → (∃ N : ℤ, 0 < N ∧ (∀ n : ℤ, 0 < n → n ≥ N → abs (1 / (n : ℝ) - 1) < ε)) := ((Parley.Items.Stdlib.Calculus.def_tends_to (x := (fun n : ℤ => 1 / (n : ℝ))) (L := (1 : ℝ)))).mp hS
  -- 2.2. instantiate ε := 1/2 in line 2.1
  have r296_1 : (0 : ℚ) < 1 / 2 := by parley_arith
  have s2_2 : ∃ N : ℤ, 0 < N ∧ (∀ n : ℤ, 0 < n → n ≥ N → abs (1 / (n : ℚ) - 1) < 1 / 2) := by (have h := (s2_1 (1 / 2 : ℝ) (by parley_side)); parley_rat_of_real h)
  -- 2.3. obtain N from line 2.2
  obtain ⟨N, s2_3a, s2_3b⟩ := s2_2
  -- 2.4. instantiate n := N + 1 in line 2.3
  have r303_1 : N + 1 ≥ N := by parley_order
  have s2_4 : abs (1 / ((N : ℚ) + 1) - 1) < 1 / 2 := by first | exact_mod_cast (s2_3b (N + 1) (by parley_side) (by parley_side)) | (have h := (s2_3b (N + 1) (by parley_side) (by parley_side)); push_cast at h ⊢; exact h) | simpa using (s2_3b (N + 1) (by parley_side) (by parley_side))
  -- 2.5. inequalities, from 2.3
  have s2_5 : N + 1 > 0 := by parley_order
  -- 2.6. mun:abs-difference-lt x := 1/(N + 1), c := 1, δ := 1/2, from 2.4
  have s2_6 : 1 - 1 / 2 < 1 / ((N : ℚ) + 1) ∧ 1 / ((N : ℚ) + 1) < 1 + 1 / 2 := ((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := 1 / ((N : ℚ) + 1)) (c := (1 : ℚ)) (δ := (1 / 2 : ℚ)))).mp s2_4
  -- 2.7. inequalities, from 2.3
  have s2_7 : 2 ≤ N + 1 := by parley_order
  -- 2.8. mun:reciprocal-order x := 2, y := N + 1, from 2.7
  have r316_1 : (2 : ℤ) > 0 := by parley_arith
  have r316_2 : N + 1 > 0 := by parley_side
  have s2_8 : 1 / ((N : ℚ) + 1) ≤ 1 / 2 := ((Parley.Items.Stdlib.Numbers.mun_reciprocal_order (x := (2 : ℚ)) (by parley_side) (y := (N : ℚ) + 1) (by parley_side))).mp (by parley_side)
  -- 2.9. inequalities, from 2.6
  have s2_9 : ¬ 1 / ((N : ℚ) + 1) ≤ 1 / 2 := by parley_side
  exact s2_9 s2_8

end Parley.Tests.Notations.Calculus.OneOverNDoesNotTendToOne
