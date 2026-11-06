module

public import SetTactics
public import Tactics
public import Parley.Items.Stdlib.Sets

/-! Written from tests/elaborator/sets-a-define-names.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.SetsADefineNames.AConjunctOfAProperty

theorem a_conjunct_of_a_property (T : Set ℤ) (N : ℤ) (hH1 : 0 < N) (hH3 : T ∈ {S ∈ 𝒫 (Set.Icc (1 : ℤ) N : Set ℤ) | N ∈ S ∧ (∀ p ∈ S, p ≤ N)}) :
    (∀ p ∈ T, p ≤ N) := by
  -- 1. def:part-builder u := T, from H3
  have s1a : T ⊆ (Set.Icc (1 : ℤ) N : Set ℤ) := by first | exact (((Parley.Items.Stdlib.Sets.def_part_builder (P := (fun S : Set ℤ => N ∈ S ∧ (∀ p ∈ S, p ≤ N))) (X := (Set.Icc (1 : ℤ) N : Set ℤ)) (u := T))).mp (by parley_set_side)).1 | exact ((((Parley.Items.Stdlib.Sets.def_part_builder (P := (fun S : Set ℤ => N ∈ S ∧ (∀ p ∈ S, p ≤ N))) (X := (Set.Icc (1 : ℤ) N : Set ℤ)) (u := T))).mp (by parley_set_side)).1).symm | simpa using (((Parley.Items.Stdlib.Sets.def_part_builder (P := (fun S : Set ℤ => N ∈ S ∧ (∀ p ∈ S, p ≤ N))) (X := (Set.Icc (1 : ℤ) N : Set ℤ)) (u := T))).mp (by parley_set_side)).1 | exact_mod_cast (((Parley.Items.Stdlib.Sets.def_part_builder (P := (fun S : Set ℤ => N ∈ S ∧ (∀ p ∈ S, p ≤ N))) (X := (Set.Icc (1 : ℤ) N : Set ℤ)) (u := T))).mp (by parley_set_side)).1 | (have h := (((Parley.Items.Stdlib.Sets.def_part_builder (P := (fun S : Set ℤ => N ∈ S ∧ (∀ p ∈ S, p ≤ N))) (X := (Set.Icc (1 : ℤ) N : Set ℤ)) (u := T))).mp (by parley_set_side)).1; parley_set_side)
  have s1b : ∀ p ∈ T, p ≤ N := by first | exact (((Parley.Items.Stdlib.Sets.def_part_builder (P := (fun S : Set ℤ => N ∈ S ∧ (∀ p ∈ S, p ≤ N))) (X := (Set.Icc (1 : ℤ) N : Set ℤ)) (u := T))).mp (by parley_set_side)).2 | exact ((((Parley.Items.Stdlib.Sets.def_part_builder (P := (fun S : Set ℤ => N ∈ S ∧ (∀ p ∈ S, p ≤ N))) (X := (Set.Icc (1 : ℤ) N : Set ℤ)) (u := T))).mp (by parley_set_side)).2).symm | simpa using (((Parley.Items.Stdlib.Sets.def_part_builder (P := (fun S : Set ℤ => N ∈ S ∧ (∀ p ∈ S, p ≤ N))) (X := (Set.Icc (1 : ℤ) N : Set ℤ)) (u := T))).mp (by parley_set_side)).2 | exact_mod_cast (((Parley.Items.Stdlib.Sets.def_part_builder (P := (fun S : Set ℤ => N ∈ S ∧ (∀ p ∈ S, p ≤ N))) (X := (Set.Icc (1 : ℤ) N : Set ℤ)) (u := T))).mp (by parley_set_side)).2 | (have h := (((Parley.Items.Stdlib.Sets.def_part_builder (P := (fun S : Set ℤ => N ∈ S ∧ (∀ p ∈ S, p ≤ N))) (X := (Set.Icc (1 : ℤ) N : Set ℤ)) (u := T))).mp (by parley_set_side)).2; parley_set_side)
  -- 2. restate 1
  have s2 : ∀ p ∈ T, p ≤ N := by intro p h_p; parley_set_side
  all_goals exact s2

end Parley.Tests.Elaborator.SetsADefineNames.AConjunctOfAProperty
