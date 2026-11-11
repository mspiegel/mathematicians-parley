module

public import Tactics
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.BigOperators
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs
public import Parley.Items.Stdlib.Calculus

/-! Written from tests/elaborator/bound-names.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.BoundNames.SeriesUnderItsOwnLetters

theorem series_under_its_own_letters (hH1 : Filter.Tendsto (fun n : ℤ => (∑ k ∈ Finset.Icc (1 : ℤ) n, (1 / ((k : ℝ) * ((k : ℝ) + 1)) : ℝ) : ℝ)) Filter.atTop (nhds 1)) :
    Filter.limUnder Filter.atTop (fun n : ℤ => ∑ k ∈ Finset.Icc (1 : ℤ) n, (1 / ((k : ℝ) * ((k : ℝ) + 1)) : ℝ)) = 1 := by
  -- 1. proof
  -- what this block shows, Lean's types give
  -- 2. def:series-sum L := 1, from H1, 1
  exact (Parley.Items.Stdlib.Calculus.def_series_sum (t := (fun k : ℤ => 1 / ((k : ℝ) * ((k : ℝ) + 1)))) (L := (1 : ℝ)) hH1)

end Parley.Tests.Elaborator.BoundNames.SeriesUnderItsOwnLetters
