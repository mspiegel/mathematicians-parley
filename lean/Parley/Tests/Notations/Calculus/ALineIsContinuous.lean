module

public import SetTactics
public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Topology.Defs.Filter
public import Parley.Items.Stdlib.Calculus

/-! Written from tests/notations/calculus.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Calculus.ALineIsContinuous

theorem a_line_is_continuous (g : ℝ → ℝ) (hH1 : Set.MapsTo g (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ) (Set.univ : Set ℝ)) (hH2 : ∀ x ∈ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ), g x = 2 * x) :
    ContinuousOn g (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ) := by
  -- 1. thm:continuous-linear D := [0, 1], m := 2, from H2
  have r91_1 : (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ) ⊆ (Set.univ : Set ℝ) := by exact (Parley.Items.Stdlib.Calculus.mun_interval_real (a := (0 : ℝ)) (b := (1 : ℝ)))
  have s1 : ContinuousOn g (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ) := by exact (Parley.Items.Stdlib.Calculus.thm_continuous_linear (g := g) (D := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) (by parley_set_side) (m := (2 : ℝ)) (by parley_set_side))
  all_goals exact s1

end Parley.Tests.Notations.Calculus.ALineIsContinuous
