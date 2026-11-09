module

public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Order.Filter.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs
public import Parley.Items.Stdlib.Calculus

/-! Written from tests/stdlib/calculus.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Calculus.ALimitAboveALateBound

theorem a_limit_above_a_late_bound (y : ℤ → ℝ) (M : ℝ) (hH3 : Filter.Tendsto (fun n : ℤ => (y n : ℝ)) Filter.atTop (nhds M)) (C : ℝ) (K : ℤ) (hH5 : 0 < K) (hH6 : ∀ n : ℤ, 0 < n → n ≥ K → C ≤ y n) :
    C ≤ M := by
  -- 1. thm:limit-at-least x := y, L := M, B := C, N := K, from H3, H6
  exact (Parley.Items.Stdlib.Calculus.thm_limit_at_least (x := y) (L := M) hH3 (B := C) (N := K) (by parley_side) hH6)

end Parley.Tests.Stdlib.Calculus.ALimitAboveALateBound
