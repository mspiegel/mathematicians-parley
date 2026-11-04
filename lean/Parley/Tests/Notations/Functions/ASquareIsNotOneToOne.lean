module

public import ArithTactics
public import PowerTactics
public import SetTactics
public import Tactics
public import Parley.Items.Stdlib.Functions

/-! Written from tests/notations/functions.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Functions.ASquareIsNotOneToOne

theorem a_square_is_not_one_to_one (f : ℝ → ℝ) (hD1 : ∀ x : ℝ, f x = x ^ 2) :
    ¬ (Set.MapsTo f (Set.univ : Set ℝ) (Set.univ : Set ℝ) ∧ Set.InjOn f (Set.univ : Set ℝ)) := by
  -- 1. D1
  have s1 : f (-1) = (-1) ^ 2 := by (try simp only [hD1]); first | done | parley_set_side
  -- 2. D1
  have s2 : f 1 = 1 ^ 2 := by (try simp only [hD1]); first | done | parley_set_side
  -- 3. calculation
  have s3 : f (-1) = f 1 := by
    calc f (-1) = (-1) ^ 2 := by parley_set_side
      _ = 1 ^ 2 := by norm_num
      _ = f 1 := by parley_set_side
  -- 4. contradiction
  have s4 : ¬ (Set.MapsTo f (Set.univ : Set ℝ) (Set.univ : Set ℝ) ∧ Set.InjOn f (Set.univ : Set ℝ)) := by
    by_contra hc_hS
    have hS : Set.MapsTo f (Set.univ : Set ℝ) (Set.univ : Set ℝ) ∧ Set.InjOn f (Set.univ : Set ℝ) := by parley_suppose hc_hS
    -- 4.1. def:one-to-one, from S
    have s4_1 : ∀ s : ℝ, ∀ t : ℝ, f s = f t → s = t := by first | exact ((Parley.Items.Stdlib.Functions.def_one_to_one (X := (Set.univ : Set ℝ)) (Y := (Set.univ : Set ℝ)) (f := f) (by parley_set_side))).mp (by parley_set_side) | exact (((Parley.Items.Stdlib.Functions.def_one_to_one (X := (Set.univ : Set ℝ)) (Y := (Set.univ : Set ℝ)) (f := f) (by parley_set_side))).mp (by parley_set_side)).symm | simpa using ((Parley.Items.Stdlib.Functions.def_one_to_one (X := (Set.univ : Set ℝ)) (Y := (Set.univ : Set ℝ)) (f := f) (by parley_set_side))).mp (by parley_set_side) | exact_mod_cast ((Parley.Items.Stdlib.Functions.def_one_to_one (X := (Set.univ : Set ℝ)) (Y := (Set.univ : Set ℝ)) (f := f) (by parley_set_side))).mp (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Functions.def_one_to_one (X := (Set.univ : Set ℝ)) (Y := (Set.univ : Set ℝ)) (f := f) (by parley_set_side))).mp (by parley_set_side); parley_set_side)
    -- 4.2. instantiate s := −1, t := 1 in line 4.1, from 3
    have s4_2 : (-1 : ℝ) = 1 := by first | linear_combination (norm := parley_norm) (s4_1 (-1 : ℝ) (1 : ℝ) (by parley_set_side)) | (have h := (s4_1 (-1 : ℝ) (1 : ℝ) (by parley_set_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (s4_1 (-1 : ℝ) (1 : ℝ) (by parley_set_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (s4_1 (-1 : ℝ) (1 : ℝ) (by parley_set_side)) | exact_mod_cast ((s4_1 (-1 : ℝ) (1 : ℝ) (by parley_set_side))).symm | (have h := (s4_1 (-1 : ℝ) (1 : ℝ) (by parley_set_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (s4_1 (-1 : ℝ) (1 : ℝ) (by parley_set_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (s4_1 (-1 : ℝ) (1 : ℝ) (by parley_set_side)); parley_int_power h) | (have h := (s4_1 (-1 : ℝ) (1 : ℝ) (by parley_set_side)); parley_set_side)
    exact absurd s4_2 (by norm_num)
    all_goals parley_set_side
  all_goals exact s4

end Parley.Tests.Notations.Functions.ASquareIsNotOneToOne
