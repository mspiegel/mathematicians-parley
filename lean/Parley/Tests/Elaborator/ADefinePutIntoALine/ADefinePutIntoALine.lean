module

public import SetTactics
public import SubstTactics
public import Tactics
public import Parley.Items.Stdlib.Sets

/-! Written from tests/elaborator/a-define-put-into-a-line.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ADefinePutIntoALine.ADefinePutIntoALine

theorem a_define_put_into_a_line {α : Type*} (A : Set α) (B : Set α) :
    A ∩ B ⊆ A := by
  set C : Set α := A ∩ B with hD1
  -- 1. mun:intersection-subset Y := A, Z := B, from D1
  have s1 : C ⊆ A := by
    try simp only [hD1] at *
    try push_cast at *
    first | exact (Parley.Items.Stdlib.Sets.mun_intersection_subset (Y := A) (Z := B)) | exact ((Parley.Items.Stdlib.Sets.mun_intersection_subset (Y := A) (Z := B))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_intersection_subset (Y := A) (Z := B)) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_intersection_subset (Y := A) (Z := B)) | (have h := (Parley.Items.Stdlib.Sets.mun_intersection_subset (Y := A) (Z := B)); parley_set_side)
  -- 2. substitute C = A ∩ B (D1) into line 1
  have s2 : A ∩ B ⊆ A := by parley_subst_at hD1 s1
  all_goals exact s2

end Parley.Tests.Elaborator.ADefinePutIntoALine.ADefinePutIntoALine
