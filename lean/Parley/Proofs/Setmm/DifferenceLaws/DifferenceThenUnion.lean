module

public import SetTactics
public import Tactics
public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/setmm/difference-laws.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.DifferenceLaws.DifferenceThenUnion

theorem difference_then_union {α : Type*} (A : Set α) (B : Set α) :
    A \ B ∪ B = A ∪ B := by
  -- 1. calculation
  have s1 : A \ B ∪ B = A ∪ B := by
    calc A \ B ∪ B = B ∪ A \ B := by exact (Parley.Items.Stdlib.Sets.mun_union_commutes (Y := A \ B) (Z := B))
      _ = B ∪ A := by exact (Parley.Items.Stdlib.Sets.mun_union_difference (Y := B) (Z := A))
      _ = A ∪ B := by exact (Parley.Items.Stdlib.Sets.mun_union_commutes (Y := B) (Z := A))
  all_goals exact s1

end Parley.Proofs.Setmm.DifferenceLaws.DifferenceThenUnion
