module

public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs
public import Parley.Items.Stdlib.Calculus

/-! Written from tests/stdlib/calculus.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Calculus.AConvergentBoundedOnBothSides

theorem a_convergent_bounded_on_both_sides (y : ℤ → ℝ) (M : ℝ) (hH3 : Filter.Tendsto (fun n : ℤ => (y n : ℝ)) Filter.atTop (nhds M)) :
    (∃ B : ℝ, ∀ m : ℤ, 0 < m → abs (y m) ≤ B) := by
  -- 1. thm:convergent-abs-bounded x := y, L := M, from H3
  exact (Parley.Items.Stdlib.Calculus.thm_convergent_abs_bounded (x := y) (L := M) hH3)

end Parley.Tests.Stdlib.Calculus.AConvergentBoundedOnBothSides
