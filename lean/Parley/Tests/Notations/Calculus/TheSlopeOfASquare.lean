module

public import SetTactics
public import Tactics
public import WholeTactics
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Normed.Field.Basic
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

namespace Parley.Tests.Notations.Calculus.TheSlopeOfASquare

theorem the_slope_of_a_square (g : ℝ → ℝ) (hH2 : ∀ x : ℝ, g x = x ^ 2) :
    (∀ x ∈ (Set.Ioo (0 : ℝ) (1 : ℝ) : Set ℝ), (deriv g) x = 2 * x) := by
  -- 1. thm:derivative-square D := ℝ, U := (0, 1), from H2
  have r140_1 : (Set.univ : Set ℝ) ⊆ (Set.univ : Set ℝ) := by exact (Parley.Items.Stdlib.Sets.mun_subset_self (X := (Set.univ : Set ℝ)))
  have r140_2 : (Set.Ioo (0 : ℝ) (1 : ℝ) : Set ℝ) ⊆ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ) := by exact (Parley.Items.Stdlib.Calculus.mun_open_within_closed (a := (0 : ℝ)) (b := (1 : ℝ)))
  have r140_3 : (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ) ⊆ (Set.univ : Set ℝ) := by exact (Parley.Items.Stdlib.Calculus.mun_interval_real (a := (0 : ℝ)) (b := (1 : ℝ)))
  have r140_4 : (Set.Ioo (0 : ℝ) (1 : ℝ) : Set ℝ) ⊆ (Set.univ : Set ℝ) := by exact (Parley.Items.Stdlib.Sets.mun_subset_transitive (X := (Set.Ioo (0 : ℝ) (1 : ℝ) : Set ℝ)) (Y := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) (Z := (Set.univ : Set ℝ)) r140_2 r140_3)
  have r140_5 : IsOpen (Set.Ioo (0 : ℝ) (1 : ℝ) : Set ℝ) := by exact (Parley.Items.Stdlib.Calculus.mun_open_interval_open (a := (0 : ℝ)) (b := (1 : ℝ)))
  exact (Parley.Items.Stdlib.Calculus.thm_derivative_square_2 (g := g) (D := (Set.univ : Set ℝ)) (U := (Set.Ioo (0 : ℝ) (1 : ℝ) : Set ℝ)) r140_1 r140_4 r140_5 (by parley_whole_side))

end Parley.Tests.Notations.Calculus.TheSlopeOfASquare
