module

public import SetTactics
public import SubstTactics
public import Tactics
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Functions
public import Parley.Items.Stdlib.Reasoning
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/wiedijk/subsets.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.Subsets.PowersetSplit

theorem powerset_split {α : Type*} (X : Set α) (a : α) (hH2 : a ∈ X) :
    𝒫 X = 𝒫 (X \ ({a} : Set α)) ∪ (fun S : Set α => S ∪ ({a} : Set α)) '' (𝒫 (X \ ({a} : Set α))) := by
  -- 1. proof
  have s1 : ∀ V ∈ 𝒫 X, V ∈ 𝒫 (X \ ({a} : Set α)) ∪ (fun S : Set α => S ∪ ({a} : Set α)) '' (𝒫 (X \ ({a} : Set α))) := by
    intro V hK1
    -- 1.1. def:powerset S := V, from K1
    have s1_1 : V ⊆ X := by exact ((Parley.Items.Stdlib.Sets.def_powerset (A := X) (S := V))).mp hK1
    -- 1.2. axi:excluded-middle P := a ∈ V
    have s1_2 : a ∈ V ∨ ¬ a ∈ V := by exact (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := a ∈ V))
    -- 1.3. cases, from 1.2
    rcases s1_2 with hC1 | hC2
    · skip
      -- 1.3.1. mun:difference-shrinks, from 1.1
      have s1_3_1 : V \ ({a} : Set α) ⊆ X \ ({a} : Set α) := by exact (Parley.Items.Stdlib.Sets.mun_difference_shrinks (X := X) (Y := V) (Z := ({a} : Set α)) s1_1)
      -- 1.3.2. def:powerset S := V ∖ {a}, from 1.3.1
      have s1_3_2 : V \ ({a} : Set α) ∈ 𝒫 (X \ ({a} : Set α)) := ((Parley.Items.Stdlib.Sets.def_powerset (A := X \ ({a} : Set α)) (S := V \ ({a} : Set α)))).mpr s1_3_1
      -- 1.3.3. mun:added-element-in-image Y := 𝒫(X ∖ {a}), s := V ∖ {a}, from 1.3.2
      have s1_3_3 : V \ ({a} : Set α) ∪ ({a} : Set α) ∈ (fun S : Set α => S ∪ ({a} : Set α)) '' (𝒫 (X \ ({a} : Set α))) := by exact (Parley.Items.Stdlib.Functions.mun_added_element_in_image (Y := 𝒫 (X \ ({a} : Set α))) (s := V \ ({a} : Set α)) (a := a) s1_3_2)
      -- 1.3.4. substitute
      have s1_3_4 : V ∈ (fun S : Set α => S ∪ ({a} : Set α)) '' (𝒫 (X \ ({a} : Set α))) := by
        have c1 : V \ ({a} : Set α) ∪ ({a} : Set α) = V := by exact (Parley.Items.Stdlib.Sets.mun_remove_and_restore (Y := V) (a := a) hC1)
        have row1 : V ∈ (fun S : Set α => S ∪ ({a} : Set α)) '' (𝒫 (X \ ({a} : Set α))) := by parley_subst_at c1 s1_3_3
        exact row1
      -- 1.3.5. mun:in-union-right, from 1.3.4
      exact (Parley.Items.Stdlib.Sets.mun_in_union_right (Y := 𝒫 (X \ ({a} : Set α))) (Z := (fun S : Set α => S ∪ ({a} : Set α)) '' (𝒫 (X \ ({a} : Set α)))) (u := V) s1_3_4)
    · skip
      -- 1.3.6. mun:subset-into-difference, from C2, 1.1
      have s1_3_6 : V ⊆ X \ ({a} : Set α) := by exact (Parley.Items.Stdlib.Sets.mun_subset_into_difference (X := X) (Y := V) (a := a) s1_1 hC2)
      -- 1.3.7. def:powerset S := V, from 1.3.6
      have s1_3_7 : V ∈ 𝒫 (X \ ({a} : Set α)) := ((Parley.Items.Stdlib.Sets.def_powerset (A := X \ ({a} : Set α)) (S := V))).mpr s1_3_6
      -- 1.3.8. mun:in-union-left, from 1.3.7
      exact (Parley.Items.Stdlib.Sets.mun_in_union_left (Y := 𝒫 (X \ ({a} : Set α))) (Z := (fun S : Set α => S ∪ ({a} : Set α)) '' (𝒫 (X \ ({a} : Set α)))) (u := V) s1_3_7)
  -- 2. def:subset, from 1
  have s2 : 𝒫 X ⊆ 𝒫 (X \ ({a} : Set α)) ∪ (fun S : Set α => S ∪ ({a} : Set α)) '' (𝒫 (X \ ({a} : Set α))) := ((Parley.Items.Stdlib.Sets.def_subset (X := 𝒫 X) (Y := 𝒫 (X \ ({a} : Set α)) ∪ (fun S : Set α => S ∪ ({a} : Set α)) '' (𝒫 (X \ ({a} : Set α)))))).mpr s1
  -- 3. mun:difference-subset
  have s3 : X \ ({a} : Set α) ⊆ X := by exact (Parley.Items.Stdlib.Sets.mun_difference_subset (X := X) (Y := ({a} : Set α)))
  -- 4. mun:powerset-monotone, from 3
  have s4 : 𝒫 (X \ ({a} : Set α)) ⊆ 𝒫 X := by exact (Parley.Items.Stdlib.Sets.mun_powerset_monotone (X := X) (Y := X \ ({a} : Set α)) s3)
  -- 5. proof
  have s5 : ∀ S ∈ 𝒫 (X \ ({a} : Set α)), S ∪ ({a} : Set α) ∈ 𝒫 X := by
    intro S hK2
    -- 5.1. def:powerset, from K2
    have s5_1 : S ⊆ X \ ({a} : Set α) := by exact ((Parley.Items.Stdlib.Sets.def_powerset (A := X \ ({a} : Set α)) (S := S))).mp hK2
    -- 5.2. mun:subset-transitive, from 3, 5.1
    have s5_2 : S ⊆ X := by exact (Parley.Items.Stdlib.Sets.mun_subset_transitive (X := S) (Y := X \ ({a} : Set α)) (Z := X) s5_1 s3)
    -- 5.3. mun:singleton-subset, from H2
    have s5_3 : ({a} : Set α) ⊆ X := by exact (Parley.Items.Stdlib.Sets.mun_singleton_subset (X := X) (a := a) hH2)
    -- 5.4. mun:union-subset, from 5.2, 5.3
    have s5_4 : S ∪ ({a} : Set α) ⊆ X := by exact (Parley.Items.Stdlib.Sets.mun_union_subset (X := S) (Y := ({a} : Set α)) (Z := X) s5_2 s5_3)
    -- 5.5. def:powerset S := S ∪ {a}, from 5.4
    exact ((Parley.Items.Stdlib.Sets.def_powerset (A := X) (S := S ∪ ({a} : Set α)))).mpr s5_4
  -- 6. mun:added-elements-stay-inside Y := 𝒫(X ∖ {a}), Z := 𝒫X, from 5
  have s6 : (fun S : Set α => S ∪ ({a} : Set α)) '' (𝒫 (X \ ({a} : Set α))) ⊆ 𝒫 X := by exact (Parley.Items.Stdlib.Functions.mun_added_elements_stay_inside (Y := 𝒫 (X \ ({a} : Set α))) (Z := 𝒫 X) (a := a) s5)
  -- 7. mun:union-subset, from 4, 6
  have s7 : 𝒫 (X \ ({a} : Set α)) ∪ (fun S : Set α => S ∪ ({a} : Set α)) '' (𝒫 (X \ ({a} : Set α))) ⊆ 𝒫 X := by exact (Parley.Items.Stdlib.Sets.mun_union_subset (X := 𝒫 (X \ ({a} : Set α))) (Y := (fun S : Set α => S ∪ ({a} : Set α)) '' (𝒫 (X \ ({a} : Set α)))) (Z := 𝒫 X) s4 s6)
  -- 8. mun:subset-antisymmetric, from 2, 7
  exact (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := 𝒫 X) (Y := 𝒫 (X \ ({a} : Set α)) ∪ (fun S : Set α => S ∪ ({a} : Set α)) '' (𝒫 (X \ ({a} : Set α)))) s2 s7)

end Parley.Proofs.Wiedijk.Subsets.PowersetSplit
