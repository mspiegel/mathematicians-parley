module

public import AlgebraTactics
public import PowerTactics
public import SetTactics
public import Tactics
public import WholeTactics
public import Parley.Items.Stdlib.Functions
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/hammack/mobius-one-to-one.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.MobiusOneToOne.MobiusOneToOne

theorem mobius_one_to_one (f : ℝ → ℝ) (hH1 : Set.MapsTo f ((Set.univ : Set ℝ) \ ({(2 : ℝ)} : Set ℝ)) (Set.univ : Set ℝ)) (hH2 : ∀ x ∈ (Set.univ : Set ℝ) \ ({(2 : ℝ)} : Set ℝ), f x = (5 * x + 1) / (x - 2)) :
    (Set.MapsTo f ((Set.univ : Set ℝ) \ ({(2 : ℝ)} : Set ℝ)) (Set.univ : Set ℝ) ∧ Set.InjOn f ((Set.univ : Set ℝ) \ ({(2 : ℝ)} : Set ℝ))) := by
  -- 1. proof
  have s1 : ∀ s ∈ (Set.univ : Set ℝ) \ ({(2 : ℝ)} : Set ℝ), ∀ t ∈ (Set.univ : Set ℝ) \ ({(2 : ℝ)} : Set ℝ), f s = f t → s = t := by
    intro s hK1
    intro t hK2
    intro hA1
    -- 1.1. mun:remove-member u := s, Y := ℝ, a := 2, from K1
    have s1_1 : s ≠ 2 := by first | exact (((Parley.Items.Stdlib.Sets.mun_remove_member (Y := (Set.univ : Set ℝ)) (a := (2 : ℝ)) (u := s))).mp (by parley_set_side)).2 | exact ((((Parley.Items.Stdlib.Sets.mun_remove_member (Y := (Set.univ : Set ℝ)) (a := (2 : ℝ)) (u := s))).mp (by parley_set_side)).2).symm | simpa using (((Parley.Items.Stdlib.Sets.mun_remove_member (Y := (Set.univ : Set ℝ)) (a := (2 : ℝ)) (u := s))).mp (by parley_set_side)).2 | exact_mod_cast (((Parley.Items.Stdlib.Sets.mun_remove_member (Y := (Set.univ : Set ℝ)) (a := (2 : ℝ)) (u := s))).mp (by parley_set_side)).2 | (have h := (((Parley.Items.Stdlib.Sets.mun_remove_member (Y := (Set.univ : Set ℝ)) (a := (2 : ℝ)) (u := s))).mp (by parley_set_side)).2; parley_set_side)
    -- 1.2. mun:remove-member u := t, Y := ℝ, a := 2, from K2
    have s1_2 : t ≠ 2 := by first | exact (((Parley.Items.Stdlib.Sets.mun_remove_member (Y := (Set.univ : Set ℝ)) (a := (2 : ℝ)) (u := t))).mp (by parley_set_side)).2 | exact ((((Parley.Items.Stdlib.Sets.mun_remove_member (Y := (Set.univ : Set ℝ)) (a := (2 : ℝ)) (u := t))).mp (by parley_set_side)).2).symm | simpa using (((Parley.Items.Stdlib.Sets.mun_remove_member (Y := (Set.univ : Set ℝ)) (a := (2 : ℝ)) (u := t))).mp (by parley_set_side)).2 | exact_mod_cast (((Parley.Items.Stdlib.Sets.mun_remove_member (Y := (Set.univ : Set ℝ)) (a := (2 : ℝ)) (u := t))).mp (by parley_set_side)).2 | (have h := (((Parley.Items.Stdlib.Sets.mun_remove_member (Y := (Set.univ : Set ℝ)) (a := (2 : ℝ)) (u := t))).mp (by parley_set_side)).2; parley_set_side)
    -- 1.3. calculation
    have s1_3 : (5 * s + 1) / (s - 2) = (5 * t + 1) / (t - 2) := by
      calc (5 * s + 1) / (s - 2) = f s := by first | linear_combination (norm := parley_norm) (hH2 s (by parley_set_side)) | (have h := (hH2 s (by parley_set_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (hH2 s (by parley_set_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (hH2 s (by parley_set_side)) | exact_mod_cast ((hH2 s (by parley_set_side))).symm | (have h := (hH2 s (by parley_set_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (hH2 s (by parley_set_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (hH2 s (by parley_set_side)); parley_int_power h) | (have h := (hH2 s (by parley_set_side)); parley_set_side)
        _ = f t := by parley_set_side
        _ = (5 * t + 1) / (t - 2) := by first | linear_combination (norm := parley_norm) (hH2 t (by parley_set_side)) | (have h := (hH2 t (by parley_set_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (hH2 t (by parley_set_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (hH2 t (by parley_set_side)) | exact_mod_cast ((hH2 t (by parley_set_side))).symm | (have h := (hH2 t (by parley_set_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (hH2 t (by parley_set_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (hH2 t (by parley_set_side)); parley_int_power h) | (have h := (hH2 t (by parley_set_side)); parley_set_side)
    -- 1.4. algebra, from 1.3
    have r29_1 : s - 2 ≠ 0 := by parley_set_side
    have r29_2 : t - 2 ≠ 0 := by parley_set_side
    have s1_4 : s = t := by linear_combination (norm := parley_field) (-(1 / 11 : ℝ) * s * t + (2 / 11 : ℝ) * s + (2 / 11 : ℝ) * t - (4 / 11 : ℝ)) * s1_3
    all_goals parley_set_side
  -- 2. def:one-to-one, from H1, 1
  have s2 : Set.MapsTo f ((Set.univ : Set ℝ) \ ({(2 : ℝ)} : Set ℝ)) (Set.univ : Set ℝ) ∧ Set.InjOn f ((Set.univ : Set ℝ) \ ({(2 : ℝ)} : Set ℝ)) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Functions.def_one_to_one (X := (Set.univ : Set ℝ) \ ({(2 : ℝ)} : Set ℝ)) (Y := (Set.univ : Set ℝ)) (f := f) (by parley_whole_side))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Functions.def_one_to_one (X := (Set.univ : Set ℝ) \ ({(2 : ℝ)} : Set ℝ)) (Y := (Set.univ : Set ℝ)) (f := f) (by parley_whole_side))).mpr (by parley_set_side); parley_set_side)
  all_goals exact s2

end Parley.Proofs.Hammack.MobiusOneToOne.MobiusOneToOne
