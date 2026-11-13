module

public import SetTactics
public import SubstTactics
public import Tactics
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Functions
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/setmm/joined-functions.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.JoinedFunctions.JoinedFunctions

theorem joined_functions {α : Type*} (A : Set α) (B : Set α) (C : Set α) (D : Set α) (F : α → α) (hH5 : Set.MapsTo F A C) (G : α → α) (hH6 : Set.MapsTo G B D) (hH7 : A ∩ B = ∅) (H : α → α) (hD1 : ∀ x : α, x ∈ A ∪ B → H x = @ite _ (x ∈ A) (Classical.propDecidable (x ∈ A)) (F x) (G x)) :
    Set.MapsTo H (A ∪ B) (C ∪ D) := by
  -- 1. proof
  have s1 : ∀ x ∈ A ∪ B, H x ∈ C ∪ D := by
    intro x hK1
    -- 1.1. def:union, from K1
    have s1_1 : x ∈ A ∨ x ∈ B := by exact ((Parley.Items.Stdlib.Sets.def_union (Y := A) (Z := B) (u := x))).mp hK1
    -- 1.2. cases, from 1.1
    rcases s1_1 with hC1 | hC2
    · skip
      -- 1.2.1. D1, from C1, K1
      have s1_2_1 : H x = F x := by simp (disch := omega) only [hD1 _ hK1, if_pos hC1]
      -- 1.2.2. mun:function-value f := F, from C1
      have s1_2_2 : F x ∈ C := by exact (Parley.Items.Stdlib.Functions.mun_function_value (D := A) (E := C) (f := F) (x := x) hC1 hH5)
      -- 1.2.3. substitute H(x) = F(x) (line 1.2.1) into line 1.2.2
      have s1_2_3 : H x ∈ C := by parley_subst_at s1_2_1 s1_2_2
      -- 1.2.4. mun:in-union-left, from 1.2.3
      exact (Parley.Items.Stdlib.Sets.mun_in_union_left (Y := C) (Z := D) (u := H x) s1_2_3)
    · skip
      -- 1.2.5. calculation
      have s1_2_5 : B ∩ A = ∅ := by
        calc B ∩ A = A ∩ B := by exact (Parley.Items.Stdlib.Sets.mun_intersection_commutes (Y := B) (Z := A))
          _ = ∅ := by exact hH7
      -- 1.2.6. mun:disjoint-member, from C2, 1.2.5
      have s1_2_6 : ¬ x ∈ A := by exact (Parley.Items.Stdlib.Sets.mun_disjoint_member (Y := B) (Z := A) (u := x) s1_2_5 hC2)
      -- 1.2.7. D1, from K1, 1.2.6
      have s1_2_7 : H x = G x := by simp (disch := omega) only [hD1 _ hK1, if_neg s1_2_6]
      -- 1.2.8. mun:function-value f := G, from C2
      have s1_2_8 : G x ∈ D := by exact (Parley.Items.Stdlib.Functions.mun_function_value (D := B) (E := D) (f := G) (x := x) hC2 hH6)
      -- 1.2.9. substitute H(x) = G(x) (line 1.2.7) into line 1.2.8
      have s1_2_9 : H x ∈ D := by parley_subst_at s1_2_7 s1_2_8
      -- 1.2.10. mun:in-union-right, from 1.2.9
      exact (Parley.Items.Stdlib.Sets.mun_in_union_right (Y := C) (Z := D) (u := H x) s1_2_9)
  -- 2. mun:function-into, from 1
  exact (Parley.Items.Stdlib.Functions.mun_function_into (E := H) (X := A ∪ B) (Y := C ∪ D) s1)

end Parley.Proofs.Setmm.JoinedFunctions.JoinedFunctions
