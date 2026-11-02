module

public import LeanBridges
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/hammack/set-meets-its-complement-in-nothing.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.SetMeetsItsComplementInNothing.SetMeetsWhatItLacksInNothing

theorem set_meets_what_it_lacks_in_nothing {α : Type*} (A : Set α) (B : Set α) :
    A ∩ (B \ A) = ∅ := by
  -- 1. proof
  have s1 : ∀ s ∈ B \ A, ¬ s ∈ A := by
    intro s hK1
    -- 1.1. def:difference u := s, Y := B, Z := A, from K1
    have s1_1 : ¬ s ∈ A := by first | exact ((Parley.Items.Stdlib.Sets.def_difference (Y := B) (Z := A) (u := s))).mp (by parley_side) | exact (((Parley.Items.Stdlib.Sets.def_difference (Y := B) (Z := A) (u := s))).mp (by parley_side)).symm | simpa using ((Parley.Items.Stdlib.Sets.def_difference (Y := B) (Z := A) (u := s))).mp (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Sets.def_difference (Y := B) (Z := A) (u := s))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Sets.def_difference (Y := B) (Z := A) (u := s))).mp (by parley_side); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := ((Parley.Items.Stdlib.Sets.def_difference (Y := B) (Z := A) (u := s))).mp (by parley_side); parley_side)
    all_goals parley_side
  -- 2. mun:disjoint-empty Y := A, Z := B ∖ A, from 1
  have s2 : A ∩ (B \ A) = ∅ := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sets.mun_disjoint_empty (Y := A) (Z := B \ A) (by parley_side)) | (have h := (Parley.Items.Stdlib.Sets.mun_disjoint_empty (Y := A) (Z := B \ A) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sets.mun_disjoint_empty (Y := A) (Z := B \ A) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_disjoint_empty (Y := A) (Z := B \ A) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Sets.mun_disjoint_empty (Y := A) (Z := B \ A) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Sets.mun_disjoint_empty (Y := A) (Z := B \ A) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sets.mun_disjoint_empty (Y := A) (Z := B \ A) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sets.mun_disjoint_empty (Y := A) (Z := B \ A) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sets.mun_disjoint_empty (Y := A) (Z := B \ A) (by parley_side)); parley_side)
  all_goals parley_side

end Parley.Proofs.Hammack.SetMeetsItsComplementInNothing.SetMeetsWhatItLacksInNothing
