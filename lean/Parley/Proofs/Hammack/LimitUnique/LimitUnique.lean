module

public import SetTactics
public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Filter.Defs
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Topology.Defs.Filter
public import Parley.Proofs.Hammack.LimitUnique.LimitOrder

/-! Written from proofs/hammack/limit-unique.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.LimitUnique.LimitUnique

theorem limit_unique (f : ℝ → ℝ) (c : ℝ) (L : ℝ) (M : ℝ) (hH5 : Filter.Tendsto f (nhdsWithin c ((Set.univ : Set ℝ) \ {c})) (nhds L)) (hH6 : Filter.Tendsto f (nhdsWithin c ((Set.univ : Set ℝ) \ {c})) (nhds M)) :
    L = M := by
  -- 1. thm:limit-order, from H5, H6
  have s1 : M ≤ L := by first | linarith [(Parley.Proofs.Hammack.LimitUnique.LimitOrder.limit_order (f := f) (c := c) (L := L) (M := M) hH5 hH6)] | (have h := (Parley.Proofs.Hammack.LimitUnique.LimitOrder.limit_order (f := f) (c := c) (L := L) (M := M) hH5 hH6); push_cast at h; linarith) | exact_mod_cast (Parley.Proofs.Hammack.LimitUnique.LimitOrder.limit_order (f := f) (c := c) (L := L) (M := M) hH5 hH6) | (have h := (Parley.Proofs.Hammack.LimitUnique.LimitOrder.limit_order (f := f) (c := c) (L := L) (M := M) hH5 hH6); parley_set_side)
  -- 2. thm:limit-order L := M, M := L, from H5, H6
  have s2 : L ≤ M := by first | linarith [(Parley.Proofs.Hammack.LimitUnique.LimitOrder.limit_order (f := f) (c := c) (L := M) (M := L) hH6 hH5)] | (have h := (Parley.Proofs.Hammack.LimitUnique.LimitOrder.limit_order (f := f) (c := c) (L := M) (M := L) hH6 hH5); push_cast at h; linarith) | exact_mod_cast (Parley.Proofs.Hammack.LimitUnique.LimitOrder.limit_order (f := f) (c := c) (L := M) (M := L) hH6 hH5) | (have h := (Parley.Proofs.Hammack.LimitUnique.LimitOrder.limit_order (f := f) (c := c) (L := M) (M := L) hH6 hH5); parley_set_side)
  -- 3. antisymmetry, from 1, 2
  have s3 : L = M := by parley_set_side
  all_goals exact s3

end Parley.Proofs.Hammack.LimitUnique.LimitUnique
