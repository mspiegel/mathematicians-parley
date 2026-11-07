module

public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Order.Filter.Defs
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Topology.Defs.Filter
public import Parley.Items.Stdlib.Calculus

/-! Written from tests/stdlib/calculus.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Calculus.ALimitBelowALateBound

theorem a_limit_below_a_late_bound (y : ℤ → ℝ) (M : ℝ) (hH3 : Filter.Tendsto (fun n : ℤ => (y n : ℝ)) Filter.atTop (nhds M)) (C : ℝ) (K : ℤ) (hH5 : 0 < K) (hH6 : ∀ n : ℤ, 0 < n → n ≥ K → y n ≤ C) :
    M ≤ C := by
  -- 1. thm:limit-at-most x := y, L := M, B := C, N := K, from H3, H6
  have s1 : M ≤ C := by first | linarith [(Parley.Items.Stdlib.Calculus.thm_limit_at_most (x := y) (L := M) hH3 (B := C) (N := K) (by parley_side) (by parley_side))] | (have h := (Parley.Items.Stdlib.Calculus.thm_limit_at_most (x := y) (L := M) hH3 (B := C) (N := K) (by parley_side) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Calculus.thm_limit_at_most (x := y) (L := M) hH3 (B := C) (N := K) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Calculus.thm_limit_at_most (x := y) (L := M) hH3 (B := C) (N := K) (by parley_side) (by parley_side)); parley_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Calculus.ALimitBelowALateBound
