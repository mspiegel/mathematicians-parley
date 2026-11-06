module

public import OrderTactics
public import PowerTactics
public import RealTactics
public import SetTactics
public import Tactics
public import WholeTactics
public import Parley.Items.Stdlib.Calculus
public import Parley.Items.Stdlib.Functions
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/hammack/two-x-minus-seven-limit.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.TwoXMinusSevenLimit.TwoXMinusSevenLimit

set_option maxHeartbeats 400000 in
theorem two_x_minus_seven_limit (f : ℝ → ℝ) (hH2 : ∀ x : ℝ, f x = 2 * x - 7) :
    Filter.Tendsto f (nhdsWithin 8 ((Set.univ : Set ℝ) \ {8})) (nhds 9) := by
  -- 1. proof
  have s1 : ∀ ε : ℝ, ε > 0 → (∃ δ : ℝ, δ > 0 ∧ (∀ x : ℝ, x ≠ 8 ∧ abs (x - 8) < δ → abs (f x - 9) < ε)) := by
    intro ε
    intro hA1
    -- 1.1. inequalities
    have s1_1 : ε / 2 > 0 := by parley_order
    -- 1.2. proof
    have s1_2 : ∀ x : ℝ, x ≠ 8 ∧ abs (x - 8) < ε / 2 → abs (f x - 9) < ε := by
      intro x
      intro hA2
      -- 1.2.1. instantiate x := x in H2
      have s1_2_1 : f x = 2 * x - 7 := by first | linear_combination (norm := parley_norm) (hH2 x) | (have h := (hH2 x); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (hH2 x); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (hH2 x) | exact_mod_cast ((hH2 x)).symm | (have h := (hH2 x); rify; linear_combination (norm := parley_norm) h) | (have h := (hH2 x); qify; linear_combination (norm := parley_norm) h) | (have h := (hH2 x); parley_int_power h) | (have h := (hH2 x); parley_set_side)
      -- 1.2.2. mun:abs-difference-lt c := 8, δ := ε/2, from A2
      have s1_2_2 : 8 - ε / 2 < x ∧ x < 8 + ε / 2 := by first | exact ((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := x) (c := (8 : ℝ)) (δ := ε / 2))).mp (by parley_set_side) | exact (((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := x) (c := (8 : ℝ)) (δ := ε / 2))).mp (by parley_set_side)).symm | simpa using ((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := x) (c := (8 : ℝ)) (δ := ε / 2))).mp (by parley_set_side) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := x) (c := (8 : ℝ)) (δ := ε / 2))).mp (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := x) (c := (8 : ℝ)) (δ := ε / 2))).mp (by parley_set_side); parley_rat_of_real h) | (have h := ((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := x) (c := (8 : ℝ)) (δ := ε / 2))).mp (by parley_set_side); parley_set_side)
      -- 1.2.3. inequalities
      have s1_2_3 : 9 - ε < 2 * x - 7 := by parley_order
      -- 1.2.4. transitivity, from 1.2.3, 1.2.1
      have s1_2_4 : 9 - ε < f x := by parley_order
      -- 1.2.5. inequalities
      have s1_2_5 : 2 * x - 7 < 9 + ε := by parley_order
      -- 1.2.6. transitivity, from 1.2.1, 1.2.5
      have s1_2_6 : f x < 9 + ε := by parley_order
      -- 1.2.7. join 1.2.4, 1.2.6
      have s1_2_7 : 9 - ε < f x ∧ f x < 9 + ε := by parley_set_side
      -- 1.2.8. mun:abs-difference-lt x := f(x), c := 9, δ := ε, from 1.2.7
      have s1_2_8 : abs (f x - 9) < ε := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := f x) (c := (9 : ℝ)) (δ := ε))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := f x) (c := (9 : ℝ)) (δ := ε))).mpr (by parley_set_side); parley_set_side)
      all_goals parley_set_side
    -- 1.3. exhibit, from 1.1, 1.2
    have s1_3 : ∃ δ : ℝ, δ > 0 ∧ (∀ x : ℝ, x ≠ 8 ∧ abs (x - 8) < δ → abs (f x - 9) < ε) := ⟨ε / 2, ⟨by parley_set_side, by parley_set_side⟩⟩
    all_goals parley_set_side
  -- 2. def:limit-at D := ℝ, c := 8, L := 9, from 1
  have r62_1 : (Set.univ : Set ℝ) ⊆ (Set.univ : Set ℝ) := by first | exact (Parley.Items.Stdlib.Sets.mun_subset_self (X := (Set.univ : Set ℝ))) | exact ((Parley.Items.Stdlib.Sets.mun_subset_self (X := (Set.univ : Set ℝ)))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_subset_self (X := (Set.univ : Set ℝ))) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_subset_self (X := (Set.univ : Set ℝ))) | (have h := (Parley.Items.Stdlib.Sets.mun_subset_self (X := (Set.univ : Set ℝ))); parley_set_side)
  have s2 : Filter.Tendsto f (nhdsWithin 8 ((Set.univ : Set ℝ) \ {8})) (nhds 9) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Calculus.def_limit_at (f := f) (D := (Set.univ : Set ℝ)) (by parley_whole_side) (c := (8 : ℝ)) (L := (9 : ℝ)))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Calculus.def_limit_at (f := f) (D := (Set.univ : Set ℝ)) (by parley_whole_side) (c := (8 : ℝ)) (L := (9 : ℝ)))).mpr (by parley_set_side); parley_set_side)
  all_goals exact s2

end Parley.Proofs.Hammack.TwoXMinusSevenLimit.TwoXMinusSevenLimit
