module

public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/setmm/difference-laws.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.DifferenceLaws.DifferenceThenUnion

theorem difference_then_union {α : Type*} (A : Set α) (B : Set α) :
    A \ B ∪ B = A ∪ B := by
  -- 1. calculation
  calc A \ B ∪ B = B ∪ A \ B := by exact (Parley.Items.Stdlib.Sets.mun_union_commutes (Y := A \ B) (Z := B))
    _ = B ∪ A := by exact (Parley.Items.Stdlib.Sets.mun_union_difference (Y := B) (Z := A))
    _ = A ∪ B := by exact (Parley.Items.Stdlib.Sets.mun_union_commutes (Y := B) (Z := A))

end Parley.Proofs.Setmm.DifferenceLaws.DifferenceThenUnion
