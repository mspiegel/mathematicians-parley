module

public import SetTactics
public import Tactics
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Functions
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/wiedijk/subsets.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.Subsets.PowersetSplitDisjoint

theorem powerset_split_disjoint {α : Type*} (X : Set α) (a : α) (hH2 : a ∈ X) :
    𝒫 (X \ ({a} : Set α)) ∩ (fun S : Set α => S ∪ ({a} : Set α)) '' (𝒫 (X \ ({a} : Set α))) = ∅ := by
  -- 1. proof
  have s1 : ∀ S ∈ 𝒫 (X \ ({a} : Set α)), ¬ S ∪ ({a} : Set α) ∈ 𝒫 (X \ ({a} : Set α)) := by
    intro S hK1
    intro hS1
    -- 1.1. mun:in-union-singleton
    have s1_1 : a ∈ S ∪ ({a} : Set α) := by exact (Parley.Items.Stdlib.Sets.mun_in_union_singleton (Y := S) (a := a))
    -- 1.2. def:powerset S := S ∪ {a}, from S1
    have s1_2 : S ∪ ({a} : Set α) ⊆ X \ ({a} : Set α) := ((Parley.Items.Stdlib.Sets.def_powerset (A := X \ ({a} : Set α)) (S := S ∪ ({a} : Set α)))).mp hS1
    -- 1.3. mun:subset-of-difference, from 1.2
    have s1_3 : ¬ a ∈ S ∪ ({a} : Set α) := by exact (Parley.Items.Stdlib.Sets.mun_subset_of_difference (X := X) (Y := S ∪ ({a} : Set α)) (a := a) s1_2)
    exact s1_3 s1_1
  -- 2. mun:added-elements-are-new Y := 𝒫(X ∖ {a}), from 1
  have s2 : ∀ V ∈ (fun S : Set α => S ∪ ({a} : Set α)) '' (𝒫 (X \ ({a} : Set α))), ¬ V ∈ 𝒫 (X \ ({a} : Set α)) := by exact (Parley.Items.Stdlib.Functions.mun_added_elements_are_new (Y := 𝒫 (X \ ({a} : Set α))) (Z := 𝒫 (X \ ({a} : Set α))) (a := a) s1)
  -- 3. mun:disjoint-empty, from 2
  exact (Parley.Items.Stdlib.Sets.mun_disjoint_empty (Y := 𝒫 (X \ ({a} : Set α))) (Z := (fun S : Set α => S ∪ ({a} : Set α)) '' (𝒫 (X \ ({a} : Set α)))) s2)

end Parley.Proofs.Wiedijk.Subsets.PowersetSplitDisjoint
