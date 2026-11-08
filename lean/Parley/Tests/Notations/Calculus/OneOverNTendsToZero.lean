module

public import OrderTactics
public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Rat.Init
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Order.Filter.Defs
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Topology.Defs.Filter
public import Parley.Items.Stdlib.Calculus
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/notations/calculus.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Calculus.OneOverNTendsToZero

set_option maxHeartbeats 400000 in
theorem one_over_n_tends_to_zero :
    Filter.Tendsto (fun n : ℤ => (1 / (n : ℝ) : ℝ)) Filter.atTop (nhds 0) := by
  -- 1. proof
  have s1 : ∀ ε : ℝ, ε > 0 → (∃ N : ℤ, 0 < N ∧ (∀ n : ℤ, 0 < n → n ≥ N → abs (1 / (n : ℝ) - 0) < ε)) := by
    intro ε
    intro hA1
    -- 1.1. obtain N: thm:archimedean x := ε, from A1
    obtain ⟨N, s1_1a, s1_1b⟩ := (Parley.Items.Stdlib.Numbers.thm_archimedean (x := ε) hA1)
    -- 1.2. proof
    have s1_2 : ∀ n : ℤ, 0 < n → n ≥ N → abs (1 / (n : ℝ) - 0) < ε := by
      intro n hK2
      intro hA2
      -- 1.2.1. mun:reciprocal-order x := N, y := n, from A2
      have r238_1 : N > 0 := by parley_order
      have r238_2 : n > 0 := by parley_order
      have s1_2_1 : 1 / (n : ℚ) ≤ 1 / (N : ℚ) := ((Parley.Items.Stdlib.Numbers.mun_reciprocal_order (x := (N : ℚ)) (by parley_side) (y := (n : ℚ)) (by parley_side))).mp (by parley_side)
      -- 1.2.2. mun:reciprocal-positive x := n
      have r243_1 : n > 0 := by parley_order
      have s1_2_2 : 1 / (n : ℚ) > 0 := (Parley.Items.Stdlib.Numbers.mun_reciprocal_positive (x := (n : ℚ)) (by parley_side))
      -- 1.2.3. inequalities
      have s1_2_3 : 0 - ε < 0 := by parley_order
      -- 1.2.4. transitivity, from 1.2.3, 1.2.2
      have s1_2_4 : 0 - ε < 1 / (n : ℝ) := by parley_order
      -- 1.2.5. inequalities, from 1.1
      have s1_2_5 : 1 / (N : ℝ) < ε := by parley_order
      -- 1.2.6. transitivity, from 1.2.1, 1.2.5
      have s1_2_6 : 1 / (n : ℝ) < 0 + ε := by parley_order
      -- 1.2.7. mun:abs-difference-lt x := 1/n, c := 0, δ := ε, from 1.2.4, 1.2.6
      exact ((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := 1 / (n : ℝ)) (c := (0 : ℝ)) (δ := ε))).mpr (by parley_side)
    -- 1.3. exhibit, from 1.2
    exact ⟨N, s1_1a, s1_2⟩
  -- 2. proof
  -- what this block shows, Lean's types give
  -- 3. def:tends-to L := 0, from 1, 2
  first | (assumption; done) | exact ((Parley.Items.Stdlib.Calculus.def_tends_to (x := (fun n : ℤ => 1 / (n : ℝ))) (L := (0 : ℝ)))).mpr s1 | (have h := ((Parley.Items.Stdlib.Calculus.def_tends_to (x := (fun n : ℤ => 1 / (n : ℝ))) (L := (0 : ℝ)))).mpr s1; parley_side)

end Parley.Tests.Notations.Calculus.OneOverNTendsToZero
