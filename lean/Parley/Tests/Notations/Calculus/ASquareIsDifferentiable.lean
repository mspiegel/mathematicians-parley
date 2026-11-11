module

public import InstanceTactics
public import SetTactics
public import Tactics
public import WholeTactics
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs
public import Parley.Items.Stdlib.Calculus
public import Parley.Items.Stdlib.Sets

/-! Written from tests/notations/calculus.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Calculus.ASquareIsDifferentiable

theorem a_square_is_differentiable (g : ℝ → ℝ) (hH2 : ∀ x : ℝ, g x = x ^ 2) :
    (∀ x ∈ (Set.Ioo (0 : ℝ) (1 : ℝ) : Set ℝ), DifferentiableAt ℝ g x) := by
  -- 1. thm:derivative-square D := ℝ, U := (0, 1), from H2
  have r127_1 : (Set.univ : Set ℝ) ⊆ (Set.univ : Set ℝ) := by exact (Parley.Items.Stdlib.Sets.mun_subset_self (X := (Set.univ : Set ℝ)))
  have r127_2 : (Set.Ioo (0 : ℝ) (1 : ℝ) : Set ℝ) ⊆ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ) := by exact (Parley.Items.Stdlib.Calculus.mun_open_within_closed (a := (0 : ℝ)) (b := (1 : ℝ)))
  have r127_3 : (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ) ⊆ (Set.univ : Set ℝ) := by exact (Parley.Items.Stdlib.Calculus.mun_interval_real (a := (0 : ℝ)) (b := (1 : ℝ)))
  have r127_4 : (Set.Ioo (0 : ℝ) (1 : ℝ) : Set ℝ) ⊆ (Set.univ : Set ℝ) := by exact (Parley.Items.Stdlib.Sets.mun_subset_transitive (X := (Set.Ioo (0 : ℝ) (1 : ℝ) : Set ℝ)) (Y := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) (Z := (Set.univ : Set ℝ)) r127_2 r127_3)
  have r127_5 : IsOpen (Set.Ioo (0 : ℝ) (1 : ℝ) : Set ℝ) := by exact (Parley.Items.Stdlib.Calculus.mun_open_interval_open (a := (0 : ℝ)) (b := (1 : ℝ)))
  have hI : ∀ x ∈ (Set.Ioo (0 : ℝ) (1 : ℝ) : Set ℝ), DifferentiableAt ℝ g x := by parley_instance ((Parley.Items.Stdlib.Calculus.thm_derivative_square_1 (g := g) (D := (Set.univ : Set ℝ)) (U := (Set.Ioo (0 : ℝ) (1 : ℝ) : Set ℝ)) r127_1 r127_4 r127_5 (by parley_whole_side)))
  exact hI

end Parley.Tests.Notations.Calculus.ASquareIsDifferentiable
