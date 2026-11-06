module

public import SetTactics
public import Tactics
public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.TypeStar
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
    have s1_1 : ¬ s ∈ A := by first | exact (((Parley.Items.Stdlib.Sets.def_difference (Y := B) (Z := A) (u := s))).mp (by parley_set_side)).2 | exact ((((Parley.Items.Stdlib.Sets.def_difference (Y := B) (Z := A) (u := s))).mp (by parley_set_side)).2).symm | simpa using (((Parley.Items.Stdlib.Sets.def_difference (Y := B) (Z := A) (u := s))).mp (by parley_set_side)).2 | exact_mod_cast (((Parley.Items.Stdlib.Sets.def_difference (Y := B) (Z := A) (u := s))).mp (by parley_set_side)).2 | (have h := (((Parley.Items.Stdlib.Sets.def_difference (Y := B) (Z := A) (u := s))).mp (by parley_set_side)).2; parley_set_side)
    all_goals exact s1_1
  -- 2. mun:disjoint-empty Y := A, Z := B ∖ A, from 1
  have s2 : A ∩ (B \ A) = ∅ := by first | exact (Parley.Items.Stdlib.Sets.mun_disjoint_empty (Y := A) (Z := B \ A) s1) | exact ((Parley.Items.Stdlib.Sets.mun_disjoint_empty (Y := A) (Z := B \ A) s1)).symm | simpa using (Parley.Items.Stdlib.Sets.mun_disjoint_empty (Y := A) (Z := B \ A) s1) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_disjoint_empty (Y := A) (Z := B \ A) s1) | (have h := (Parley.Items.Stdlib.Sets.mun_disjoint_empty (Y := A) (Z := B \ A) s1); parley_set_side)
  all_goals exact s2

end Parley.Proofs.Hammack.SetMeetsItsComplementInNothing.SetMeetsWhatItLacksInNothing
