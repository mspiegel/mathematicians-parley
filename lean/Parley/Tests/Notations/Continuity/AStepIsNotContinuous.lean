module

public import ArithTactics
public import OrderTactics
public import RealTactics
public import SetTactics
public import SubstTactics
public import Tactics
public import WholeTactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.Ring.Unbundled.Rat
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Rat.Defs
public import Mathlib.Data.Rat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Order.Lattice
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Set
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Topology.Defs.Filter
public import Parley.Items.Stdlib.Calculus
public import Parley.Items.Stdlib.Functions
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/notations/continuity.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Continuity.AStepIsNotContinuous

set_option maxHeartbeats 600000 in
theorem a_step_is_not_continuous (f : ℝ → ℝ) (hD1 : ∀ x : ℝ, x ∈ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ) → f x = (@ite _ (x < 1 / 2) (Classical.propDecidable (x < 1 / 2)) 0 1 : ℝ)) :
    ¬ ContinuousOn f (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ) := by
  -- 1. def:interval a := 0, b := 1, x := 1/2
  have r22_1 : (0 : ℚ) ≤ 1 / 2 := by parley_arith
  have r22_2 : (1 / 2 : ℚ) ≤ 1 := by parley_arith
  have s1 : (1 / 2 : ℝ) ∈ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ) := ((Parley.Items.Stdlib.Calculus.def_interval (x := (1 / 2 : ℝ)) (a := (0 : ℝ)) (b := (1 : ℝ)))).mpr (by parley_set_side)
  -- 2. arithmetic
  have s2 : ¬ (1 / 2 : ℚ) < 1 / 2 := by parley_arith
  -- 3. D1, from 1, 2
  have s3 : f (1 / 2) = 1 := by (try simp only [hD1]); first | done | parley_set_side
  -- 4. contradiction
  intro hS
  -- 4.1. def:continuous-on D := [0, 1], from S
  have r37_1 : (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ) ⊆ (Set.univ : Set ℝ) := by exact (Parley.Items.Stdlib.Calculus.mun_interval_real (a := (0 : ℝ)) (b := (1 : ℝ)))
  have r37_2 : ∀ x ∈ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ), True := by intro x h_x; parley_set_side
  have r37_4 : Set.MapsTo f (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ) (Set.univ : Set ℝ) := by exact (Parley.Items.Stdlib.Functions.mun_function_into (E := f) (X := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) (Y := (Set.univ : Set ℝ)) (by parley_set_side) (by parley_whole_side))
  have s4_1 : ∀ c ∈ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ), ∀ ε : ℝ, ε > 0 → (∃ δ : ℝ, δ > 0 ∧ (∀ x ∈ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ), abs (x - c) < δ → abs (f x - f c) < ε)) := ((Parley.Items.Stdlib.Calculus.def_continuous_on (f := f) (D := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) r37_1)).mp hS
  -- 4.2. instantiate c := 1/2, ε := 1/2 in line 4.1, from 1
  have r45_1 : (0 : ℚ) < 1 / 2 := by parley_arith
  have s4_2 : ∃ δ : ℝ, δ > 0 ∧ (∀ x ∈ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ), abs (x - 1 / 2) < δ → abs (f x - f (1 / 2)) < 1 / 2) := by first | exact (s4_1 (1 / 2 : ℝ) (by parley_set_side) (1 / 2 : ℝ) (by parley_set_side)) | exact ((s4_1 (1 / 2 : ℝ) (by parley_set_side) (1 / 2 : ℝ) (by parley_set_side))).symm | simpa using (s4_1 (1 / 2 : ℝ) (by parley_set_side) (1 / 2 : ℝ) (by parley_set_side)) | exact_mod_cast (s4_1 (1 / 2 : ℝ) (by parley_set_side) (1 / 2 : ℝ) (by parley_set_side)) | (have h := (s4_1 (1 / 2 : ℝ) (by parley_set_side) (1 / 2 : ℝ) (by parley_set_side)); parley_rat_of_real h) | (have h := (s4_1 (1 / 2 : ℝ) (by parley_set_side) (1 / 2 : ℝ) (by parley_set_side)); parley_set_side)
  -- 4.3. obtain δ from line 4.2
  obtain ⟨δ, ⟨s4_3a, s4_3b⟩⟩ := s4_2
  set m : ℝ := min δ (1 / 2) with hD2
  have hD2_kind : True := by first | exact (Parley.Items.Stdlib.Numbers.mun_min_real (x := δ) (y := (1 / 2 : ℝ))) | exact ((Parley.Items.Stdlib.Numbers.mun_min_real (x := δ) (y := (1 / 2 : ℝ)))).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_min_real (x := δ) (y := (1 / 2 : ℝ))) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_min_real (x := δ) (y := (1 / 2 : ℝ))) | (have h := (Parley.Items.Stdlib.Numbers.mun_min_real (x := δ) (y := (1 / 2 : ℝ))); parley_rat_of_real h) | (have h := (Parley.Items.Stdlib.Numbers.mun_min_real (x := δ) (y := (1 / 2 : ℝ))); parley_set_side)
  set x₁ : ℝ := 1 / 2 - m / 2 with hD3
  have hD3_kind : True := by parley_set_side
  -- 4.4. mun:lt-min z := 0, x := δ, y := 1/2, from 4.3
  have r62_1 : (0 : ℚ) < 1 / 2 := by parley_arith
  have s4_4 : 0 < min δ (1 / 2) := ((Parley.Items.Stdlib.Numbers.mun_lt_min (z := (0 : ℝ)) (x := δ) (y := (1 / 2 : ℝ)))).mpr (by parley_set_side)
  -- 4.5. mun:min-le x := δ, y := 1/2
  have s4_5a : min δ (1 / 2) ≤ δ := (Parley.Items.Stdlib.Numbers.mun_min_le_1 (x := δ) (y := (1 / 2 : ℝ)))
  have s4_5b : min δ (1 / 2) ≤ 1 / 2 := (Parley.Items.Stdlib.Numbers.mun_min_le_2 (x := δ) (y := (1 / 2 : ℝ)))
  -- 4.6. inequalities
  have s4_6 : 0 < min δ (1 / 2) / 2 := by parley_order
  -- 4.7. inequalities
  have s4_7 : 1 / 2 - min δ (1 / 2) / 2 < 1 / 2 := by parley_order
  -- 4.8. inequalities, from D2, D3, 4.7
  have s4_8 : x₁ < 1 / 2 := by parley_order
  -- 4.9. inequalities
  have s4_9 : 1 / 2 - min δ (1 / 2) / 2 ≥ 1 / 4 := by parley_order
  -- 4.10. inequalities, from 4.8
  have s4_10 : x₁ < 1 := by parley_order
  -- 4.11. def:interval a := 0, b := 1, x := x₁, from D3
  have r94_1 : 0 ≤ x₁ := by parley_order
  have r94_2 : x₁ ≤ 1 := by parley_set_side
  have s4_11 : x₁ ∈ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Calculus.def_interval (x := 1 / 2 - m / 2) (a := (0 : ℝ)) (b := (1 : ℝ)))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Calculus.def_interval (x := 1 / 2 - m / 2) (a := (0 : ℝ)) (b := (1 : ℝ)))).mpr (by parley_set_side); parley_set_side)
  -- 4.12. inequalities
  have s4_12 : -δ ≤ -min δ (1 / 2) := by parley_order
  -- 4.13. mun:abs-difference-lt x := x₁, c := 1/2, from D3
  have r106_1 : 1 / 2 - δ < x₁ := by parley_order
  have r106_2 : x₁ < 1 / 2 + δ := by parley_order
  have s4_13 : abs (x₁ - 1 / 2) < δ := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := 1 / 2 - m / 2) (c := (1 / 2 : ℝ)) (δ := δ))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := 1 / 2 - m / 2) (c := (1 / 2 : ℝ)) (δ := δ))).mpr (by parley_set_side); parley_set_side)
  -- 4.14. instantiate x := x₁ in line 4.3, from 4.11, 4.13
  have s4_14 : abs (f x₁ - f (1 / 2)) < 1 / 2 := by first | linarith [(s4_3b x₁ (by parley_set_side) (by parley_set_side))] | (have h := (s4_3b x₁ (by parley_set_side) (by parley_set_side)); push_cast at h; linarith) | exact_mod_cast (s4_3b x₁ (by parley_set_side) (by parley_set_side)) | (have h := (s4_3b x₁ (by parley_set_side) (by parley_set_side)); parley_set_side)
  -- 4.15. D1, from 4.8, 4.11
  have s4_15 : f x₁ = 0 := by (try simp only [hD1]); first | done | parley_set_side
  -- 4.16. substitute f(x₁) = 0 (line 4.15) into line 4.14
  have s4_16 : abs (0 - f (1 / 2)) < 1 / 2 := by parley_subst_at s4_15 s4_14
  -- 4.17. substitute f(1/2) = 1 (line 3) into line 4.16
  have s4_17 : (abs (0 - 1) : ℝ) < 1 / 2 := by parley_subst_at s3 s4_16
  -- 4.18. arithmetic
  have s4_18 : (0 - 1 : ℤ) < 0 := by parley_arith
  -- 4.19. def:abs x := 0 − 1, from 4.18
  have s4_19 : (abs (0 - 1) : ℤ) = -(0 - 1) := (Parley.Items.Stdlib.Numbers.def_abs_2 (x := (0 - 1 : ℤ))) s4_18
  -- 4.20. calculation
  have s4_20 : (-(0 - 1) : ℚ) < 1 / 2 := by
    calc (-(0 - 1) : ℚ) = abs (0 - 1) := by parley_set_side
      _ < 1 / 2 := by parley_set_side
  exact absurd s4_20 (by norm_num)

end Parley.Tests.Notations.Continuity.AStepIsNotContinuous
