module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.BigOperators
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

/-! Written from tests/elaborator/textbook-exercise-shapes.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.TextbookExerciseShapes.ADefineJoinedUnderALimit

theorem a_define_joined_under_a_limit (t : ℤ → ℝ) (K : ℝ) (S : ℤ → ℝ) (hD2 : ∀ n : ℤ, 0 < n → S n = (∑ k ∈ Finset.Icc (1 : ℤ) n, (t k : ℝ))) (hH3 : Filter.Tendsto (fun n : ℤ => (S n : ℝ)) Filter.atTop (nhds K)) :
    Filter.Tendsto (fun n : ℤ => (∑ k ∈ Finset.Icc (1 : ℤ) n, (t k : ℝ) : ℝ)) Filter.atTop (nhds K) := by
  -- 1. restate D2, H3
  exact (hH3).congr' (Filter.eventually_atTop.mpr ⟨1, by intro n hn; rw [hD2 n (by omega)]⟩)

end Parley.Tests.Elaborator.TextbookExerciseShapes.ADefineJoinedUnderALimit
