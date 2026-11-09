module

public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Order.Filter.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs
public import Parley.Items.Stdlib.Calculus

/-! Written from tests/stdlib/calculus.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Calculus.AnIncreasingBoundedSequenceConverges

theorem an_increasing_bounded_sequence_converges (y : ℤ → ℝ) (hH2 : ∀ m : ℤ, 0 < m → y m ≤ y (m + 1)) (C : ℝ) (hH4 : ∀ m : ℤ, 0 < m → y m ≤ C) :
    (∃ M : ℝ, Filter.Tendsto (fun n : ℤ => (y n : ℝ)) Filter.atTop (nhds M)) := by
  -- 1. thm:monotone-limit x := y, B := C, from H2, H4
  exact (Parley.Items.Stdlib.Calculus.thm_monotone_limit (x := y) hH2 (B := C) hH4)

end Parley.Tests.Stdlib.Calculus.AnIncreasingBoundedSequenceConverges
