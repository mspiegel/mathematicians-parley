module

public import SetTactics
public import Tactics
public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/setmm/difference-laws.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.DifferenceLaws.DifferenceThenUnion

theorem difference_then_union {α : Type*} (A : Set α) (B : Set α) :
    A \ B ∪ B = A ∪ B := by
  -- 1. calculation
  have s1 : A \ B ∪ B = A ∪ B := by
    calc A \ B ∪ B = B ∪ A \ B := by first | exact (Parley.Items.Stdlib.Sets.mun_union_commutes (Y := A \ B) (Z := B)) | exact ((Parley.Items.Stdlib.Sets.mun_union_commutes (Y := A \ B) (Z := B))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_union_commutes (Y := A \ B) (Z := B)) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_union_commutes (Y := A \ B) (Z := B)) | (have h := (Parley.Items.Stdlib.Sets.mun_union_commutes (Y := A \ B) (Z := B)); parley_set_side)
      _ = B ∪ A := by first | exact (Parley.Items.Stdlib.Sets.mun_union_difference (Y := B) (Z := A)) | exact ((Parley.Items.Stdlib.Sets.mun_union_difference (Y := B) (Z := A))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_union_difference (Y := B) (Z := A)) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_union_difference (Y := B) (Z := A)) | (have h := (Parley.Items.Stdlib.Sets.mun_union_difference (Y := B) (Z := A)); parley_set_side)
      _ = A ∪ B := by first | exact (Parley.Items.Stdlib.Sets.mun_union_commutes (Y := B) (Z := A)) | exact ((Parley.Items.Stdlib.Sets.mun_union_commutes (Y := B) (Z := A))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_union_commutes (Y := B) (Z := A)) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_union_commutes (Y := B) (Z := A)) | (have h := (Parley.Items.Stdlib.Sets.mun_union_commutes (Y := B) (Z := A)); parley_set_side)
  all_goals exact s1

end Parley.Proofs.Setmm.DifferenceLaws.DifferenceThenUnion
