module

public import RealTactics
public import SetTactics
public import SubstTactics
public import Tactics
public import WholeTactics
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs
public import Parley.Items.Stdlib.Calculus
public import Parley.Items.Stdlib.Sets

/-! Written from tests/stdlib/calculus.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Calculus.DerivativeOfADifference

theorem derivative_of_a_difference (f : ℝ → ℝ) (hH2 : ∀ x ∈ (Set.univ : Set ℝ), DifferentiableAt ℝ f x) (g : ℝ → ℝ) (hH4 : ∀ x : ℝ, g x = 3 * x) (F : ℝ → ℝ) (hH6 : ∀ x : ℝ, F x = f x - g x) :
    (∀ x : ℝ, (deriv F) x = (deriv f) x - 3) := by
  -- 1. mun:subset-self X := ℝ
  have s1 : (Set.univ : Set ℝ) ⊆ (Set.univ : Set ℝ) := by exact (Parley.Items.Stdlib.Sets.mun_subset_self (X := (Set.univ : Set ℝ)))
  -- 2. mun:reals-open
  have s2 : IsOpen (Set.univ : Set ℝ) := by exact Parley.Items.Stdlib.Calculus.mun_reals_open
  -- 3. thm:derivative-linear D := ℝ, U := ℝ, m := 3, from H4, 1, 2
  have s3 : ∀ x ∈ (Set.univ : Set ℝ), DifferentiableAt ℝ g x := by first | exact (Parley.Items.Stdlib.Calculus.thm_derivative_linear_1 (g := g) (D := (Set.univ : Set ℝ)) (U := (Set.univ : Set ℝ)) (by parley_whole_side) (by parley_whole_side) (by parley_whole_side) (m := (3 : ℝ)) (by parley_whole_side)) | exact ((Parley.Items.Stdlib.Calculus.thm_derivative_linear_1 (g := g) (D := (Set.univ : Set ℝ)) (U := (Set.univ : Set ℝ)) (by parley_whole_side) (by parley_whole_side) (by parley_whole_side) (m := (3 : ℝ)) (by parley_whole_side))).symm | simpa using (Parley.Items.Stdlib.Calculus.thm_derivative_linear_1 (g := g) (D := (Set.univ : Set ℝ)) (U := (Set.univ : Set ℝ)) (by parley_whole_side) (by parley_whole_side) (by parley_whole_side) (m := (3 : ℝ)) (by parley_whole_side)) | exact_mod_cast (Parley.Items.Stdlib.Calculus.thm_derivative_linear_1 (g := g) (D := (Set.univ : Set ℝ)) (U := (Set.univ : Set ℝ)) (by parley_whole_side) (by parley_whole_side) (by parley_whole_side) (m := (3 : ℝ)) (by parley_whole_side)) | (have h := (Parley.Items.Stdlib.Calculus.thm_derivative_linear_1 (g := g) (D := (Set.univ : Set ℝ)) (U := (Set.univ : Set ℝ)) (by parley_whole_side) (by parley_whole_side) (by parley_whole_side) (m := (3 : ℝ)) (by parley_whole_side)); parley_rat_of_real h) | (have h := (Parley.Items.Stdlib.Calculus.thm_derivative_linear_1 (g := g) (D := (Set.univ : Set ℝ)) (U := (Set.univ : Set ℝ)) (by parley_whole_side) (by parley_whole_side) (by parley_whole_side) (m := (3 : ℝ)) (by parley_whole_side)); parley_set_side)
  -- 4. thm:derivative-linear D := ℝ, U := ℝ, m := 3, from H4, 1, 2
  have s4 : ∀ x : ℝ, (deriv g) x = 3 := by first | exact (Parley.Items.Stdlib.Calculus.thm_derivative_linear_2 (g := g) (D := (Set.univ : Set ℝ)) (U := (Set.univ : Set ℝ)) (by parley_whole_side) (by parley_whole_side) (by parley_whole_side) (m := (3 : ℝ)) (by parley_whole_side)) | exact ((Parley.Items.Stdlib.Calculus.thm_derivative_linear_2 (g := g) (D := (Set.univ : Set ℝ)) (U := (Set.univ : Set ℝ)) (by parley_whole_side) (by parley_whole_side) (by parley_whole_side) (m := (3 : ℝ)) (by parley_whole_side))).symm | simpa using (Parley.Items.Stdlib.Calculus.thm_derivative_linear_2 (g := g) (D := (Set.univ : Set ℝ)) (U := (Set.univ : Set ℝ)) (by parley_whole_side) (by parley_whole_side) (by parley_whole_side) (m := (3 : ℝ)) (by parley_whole_side)) | exact_mod_cast (Parley.Items.Stdlib.Calculus.thm_derivative_linear_2 (g := g) (D := (Set.univ : Set ℝ)) (U := (Set.univ : Set ℝ)) (by parley_whole_side) (by parley_whole_side) (by parley_whole_side) (m := (3 : ℝ)) (by parley_whole_side)) | (have h := (Parley.Items.Stdlib.Calculus.thm_derivative_linear_2 (g := g) (D := (Set.univ : Set ℝ)) (U := (Set.univ : Set ℝ)) (by parley_whole_side) (by parley_whole_side) (by parley_whole_side) (m := (3 : ℝ)) (by parley_whole_side)); parley_rat_of_real h) | (have h := (Parley.Items.Stdlib.Calculus.thm_derivative_linear_2 (g := g) (D := (Set.univ : Set ℝ)) (U := (Set.univ : Set ℝ)) (by parley_whole_side) (by parley_whole_side) (by parley_whole_side) (m := (3 : ℝ)) (by parley_whole_side)); parley_set_side)
  -- 5. thm:derivative-difference D := ℝ, U := ℝ, from H2, H6, 1, 3
  have s5 : ∀ x : ℝ, (deriv F) x = (deriv f) x - (deriv g) x := by first | exact (Parley.Items.Stdlib.Calculus.thm_derivative_difference_2 (F := F) (f := f) (g := g) (D := (Set.univ : Set ℝ)) (U := (Set.univ : Set ℝ)) (by parley_whole_side) (by parley_whole_side) (by parley_whole_side) (by parley_whole_side) (by parley_whole_side)) | exact ((Parley.Items.Stdlib.Calculus.thm_derivative_difference_2 (F := F) (f := f) (g := g) (D := (Set.univ : Set ℝ)) (U := (Set.univ : Set ℝ)) (by parley_whole_side) (by parley_whole_side) (by parley_whole_side) (by parley_whole_side) (by parley_whole_side))).symm | simpa using (Parley.Items.Stdlib.Calculus.thm_derivative_difference_2 (F := F) (f := f) (g := g) (D := (Set.univ : Set ℝ)) (U := (Set.univ : Set ℝ)) (by parley_whole_side) (by parley_whole_side) (by parley_whole_side) (by parley_whole_side) (by parley_whole_side)) | exact_mod_cast (Parley.Items.Stdlib.Calculus.thm_derivative_difference_2 (F := F) (f := f) (g := g) (D := (Set.univ : Set ℝ)) (U := (Set.univ : Set ℝ)) (by parley_whole_side) (by parley_whole_side) (by parley_whole_side) (by parley_whole_side) (by parley_whole_side)) | (have h := (Parley.Items.Stdlib.Calculus.thm_derivative_difference_2 (F := F) (f := f) (g := g) (D := (Set.univ : Set ℝ)) (U := (Set.univ : Set ℝ)) (by parley_whole_side) (by parley_whole_side) (by parley_whole_side) (by parley_whole_side) (by parley_whole_side)); parley_set_side)
  -- 6. proof
  intro x
  -- 6.1. instantiate x := x in line 5
  have s6_1 : (deriv F) x = (deriv f) x - (deriv g) x := by exact (s5 x)
  -- 6.2. substitute
  have c1 : (deriv g) x = 3 := by exact (s4 x)
  have row1 : (deriv F) x = (deriv f) x - 3 := by parley_subst_at c1 s6_1
  exact row1

end Parley.Tests.Stdlib.Calculus.DerivativeOfADifference
