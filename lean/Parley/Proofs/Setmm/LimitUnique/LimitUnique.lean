module

public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Order.Filter.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs
public import Parley.Proofs.Setmm.LimitUnique.LimitAtMost

/-! Written from proofs/setmm/limit-unique.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.LimitUnique.LimitUnique

theorem limit_unique (x : ℤ → ℝ) (A : ℝ) (B : ℝ) (hH4 : Filter.Tendsto (fun n : ℤ => (x n : ℝ)) Filter.atTop (nhds A)) (hH5 : Filter.Tendsto (fun n : ℤ => (x n : ℝ)) Filter.atTop (nhds B)) :
    A = B := by
  -- 1. thm:limit-at-most, from H4, H5
  have s1 : A ≤ B := by exact (Parley.Proofs.Setmm.LimitUnique.LimitAtMost.limit_at_most (x := x) (A := A) (B := B) hH4 hH5)
  -- 2. thm:limit-at-most A := B, B := A, from H4, H5
  have s2 : B ≤ A := by exact (Parley.Proofs.Setmm.LimitUnique.LimitAtMost.limit_at_most (x := x) (A := B) (B := A) hH5 hH4)
  -- 3. antisymmetry, from 1, 2
  parley_side

end Parley.Proofs.Setmm.LimitUnique.LimitUnique
