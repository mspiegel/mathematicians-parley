module

public import SetTactics
public import Tactics
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/hammack/divisors-of-k-divide-k-squared.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.DivisorsOfKDivideKSquared.DivisorsOfKDivideKSquared

theorem divisors_of_k_divide_k_squared (k : ℤ) :
    {n : ℤ | n ∣ k} ⊆ {n : ℤ | n ∣ k ^ 2} := by
  -- 1. proof
  have s1 : ∀ t ∈ {n : ℤ | n ∣ k}, t ∈ {n : ℤ | n ∣ k ^ 2} := by
    intro t hK1
    -- 1.1. def:set-builder, from K1
    have s1_1 : t ∣ k := by first | exact (((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun n : ℤ => n ∣ k)) (X := (Set.univ : Set ℤ)) (u := t))).mp (by parley_set_side)).2 | exact ((((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun n : ℤ => n ∣ k)) (X := (Set.univ : Set ℤ)) (u := t))).mp (by parley_set_side)).2).symm | simpa using (((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun n : ℤ => n ∣ k)) (X := (Set.univ : Set ℤ)) (u := t))).mp (by parley_set_side)).2 | exact_mod_cast (((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun n : ℤ => n ∣ k)) (X := (Set.univ : Set ℤ)) (u := t))).mp (by parley_set_side)).2 | (have h := (((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun n : ℤ => n ∣ k)) (X := (Set.univ : Set ℤ)) (u := t))).mp (by parley_set_side)).2; parley_set_side)
    -- 1.2. obtain c: def:divides d := t, n := k, from 1.1
    obtain ⟨c, s1_2⟩ := ((Parley.Items.Stdlib.Divisibility.def_divides (d := t) (n := k))).mp (by parley_set_side)
    -- 1.3. algebra, from 1.1, 1.2
    have s1_3 : k ^ 2 = t * (c * k) := by linear_combination (norm := parley_norm) (k) * s1_2
    -- 1.4. def:divides d := t, n := k², from 1.1, 1.3
    have s1_4 : t ∣ k ^ 2 := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_divides (d := t) (n := k ^ 2))).mpr ⟨c * k, by parley_set_side⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_divides (d := t) (n := k ^ 2))).mpr ⟨c * k, by parley_set_side⟩; parley_set_side)
    -- 1.5. def:set-builder, from 1.1, 1.4
    have s1_5 : t ∈ {n : ℤ | n ∣ k ^ 2} := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun n : ℤ => n ∣ k ^ 2)) (X := (Set.univ : Set ℤ)) (u := t))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun n : ℤ => n ∣ k ^ 2)) (X := (Set.univ : Set ℤ)) (u := t))).mpr (by parley_set_side); parley_set_side)
    all_goals exact s1_5
  -- 2. def:subset, from 1
  have s2 : {n : ℤ | n ∣ k} ⊆ {n : ℤ | n ∣ k ^ 2} := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_subset (X := {n : ℤ | n ∣ k}) (Y := {n : ℤ | n ∣ k ^ 2}))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := {n : ℤ | n ∣ k}) (Y := {n : ℤ | n ∣ k ^ 2}))).mpr (by parley_set_side); parley_set_side)
  all_goals exact s2

end Parley.Proofs.Hammack.DivisorsOfKDivideKSquared.DivisorsOfKDivideKSquared
