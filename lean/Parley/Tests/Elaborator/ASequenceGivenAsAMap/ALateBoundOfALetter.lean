module

public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Order.Filter.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs
public import Parley.Items.Stdlib.Calculus

/-! Written from tests/elaborator/a-sequence-given-as-a-map.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ASequenceGivenAsAMap.ALateBoundOfALetter

theorem a_late_bound_of_a_letter (y : ℤ → ℝ) (L : ℝ) (hH3 : Filter.Tendsto (fun n : ℤ => (y n : ℝ)) Filter.atTop (nhds L)) (hH4 : ∀ i : ℤ, 0 < i → i ≥ 1 → y i ≤ 1) :
    L ≤ 1 := by
  -- 1. thm:limit-at-most x := y, B := 1, N := 1, from H3, H4
  exact (Parley.Items.Stdlib.Calculus.thm_limit_at_most (x := y) (L := L) hH3 (B := (1 : ℝ)) (N := (1 : ℤ)) (by norm_num) hH4)

end Parley.Tests.Elaborator.ASequenceGivenAsAMap.ALateBoundOfALetter
