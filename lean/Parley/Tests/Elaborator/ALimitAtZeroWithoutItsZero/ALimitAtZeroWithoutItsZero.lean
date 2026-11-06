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

/-! Written from tests/elaborator/a-limit-at-zero-without-its-zero.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ALimitAtZeroWithoutItsZero.ALimitAtZeroWithoutItsZero

set_option maxHeartbeats 400000 in
theorem a_limit_at_zero_without_its_zero (f : ℝ → ℝ) (hH2 : ∀ x : ℝ, f x = x + 2) :
    Filter.Tendsto f (nhdsWithin 0 ((Set.univ : Set ℝ) \ {0})) (nhds 2) := by
  -- 1. proof
  have s1 : ∀ ε : ℝ, ε > 0 → (∃ δ : ℝ, δ > 0 ∧ (∀ x : ℝ, x ≠ 0 ∧ abs x < δ → abs (f x - 2) < ε)) := by
    intro ε
    intro hA1
    -- 1.1. proof
    have s1_1 : ∀ x : ℝ, x ≠ 0 ∧ abs x < ε → abs (f x - 2) < ε := by
      intro x
      intro hA2
      -- 1.1.1. instantiate x := x in H2
      have s1_1_1 : f x = x + 2 := by first | linear_combination (norm := parley_norm) (hH2 x) | (have h := (hH2 x); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (hH2 x); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (hH2 x) | exact_mod_cast ((hH2 x)).symm | (have h := (hH2 x); rify; linear_combination (norm := parley_norm) h) | (have h := (hH2 x); qify; linear_combination (norm := parley_norm) h) | (have h := (hH2 x); parley_int_power h) | (have h := (hH2 x); parley_set_side)
      -- 1.1.2. mun:abs-difference-lt c := 0, δ := ε, from A2
      have s1_1_2 : 0 - ε < x ∧ x < 0 + ε := by first | exact ((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := x) (c := (0 : ℝ)) (δ := ε))).mp (by parley_set_side) | exact (((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := x) (c := (0 : ℝ)) (δ := ε))).mp (by parley_set_side)).symm | simpa using ((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := x) (c := (0 : ℝ)) (δ := ε))).mp (by parley_set_side) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := x) (c := (0 : ℝ)) (δ := ε))).mp (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := x) (c := (0 : ℝ)) (δ := ε))).mp (by parley_set_side); parley_rat_of_real h) | (have h := ((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := x) (c := (0 : ℝ)) (δ := ε))).mp (by parley_set_side); parley_set_side)
      -- 1.1.3. inequalities
      have s1_1_3 : 2 - ε < x + 2 := by parley_order
      -- 1.1.4. transitivity, from 1.1.3, 1.1.1
      have s1_1_4 : 2 - ε < f x := by parley_order
      -- 1.1.5. inequalities
      have s1_1_5 : x + 2 < 2 + ε := by parley_order
      -- 1.1.6. transitivity, from 1.1.1, 1.1.5
      have s1_1_6 : f x < 2 + ε := by parley_order
      -- 1.1.7. join 1.1.4, 1.1.6
      have s1_1_7 : 2 - ε < f x ∧ f x < 2 + ε := by parley_set_side
      -- 1.1.8. mun:abs-difference-lt x := f(x), c := 2, δ := ε, from 1.1.7
      have s1_1_8 : abs (f x - 2) < ε := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := f x) (c := (2 : ℝ)) (δ := ε))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := f x) (c := (2 : ℝ)) (δ := ε))).mpr (by parley_set_side); parley_set_side)
      all_goals parley_set_side
    -- 1.2. exhibit, from A1, 1.1
    have s1_2 : ∃ δ : ℝ, δ > 0 ∧ (∀ x : ℝ, x ≠ 0 ∧ abs x < δ → abs (f x - 2) < ε) := ⟨ε, ⟨by parley_set_side, by parley_set_side⟩⟩
    all_goals parley_set_side
  -- 2. def:limit-at D := ℝ, c := 0, L := 2, from 1
  have r57_1 : (Set.univ : Set ℝ) ⊆ (Set.univ : Set ℝ) := by first | exact (Parley.Items.Stdlib.Sets.mun_subset_self (X := (Set.univ : Set ℝ))) | exact ((Parley.Items.Stdlib.Sets.mun_subset_self (X := (Set.univ : Set ℝ)))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_subset_self (X := (Set.univ : Set ℝ))) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_subset_self (X := (Set.univ : Set ℝ))) | (have h := (Parley.Items.Stdlib.Sets.mun_subset_self (X := (Set.univ : Set ℝ))); parley_set_side)
  have s2 : Filter.Tendsto f (nhdsWithin 0 ((Set.univ : Set ℝ) \ {0})) (nhds 2) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Calculus.def_limit_at (f := f) (D := (Set.univ : Set ℝ)) (by parley_whole_side) (c := (0 : ℝ)) (L := (2 : ℝ)))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Calculus.def_limit_at (f := f) (D := (Set.univ : Set ℝ)) (by parley_whole_side) (c := (0 : ℝ)) (L := (2 : ℝ)))).mpr (by parley_set_side); parley_set_side)
  all_goals exact s2

end Parley.Tests.Elaborator.ALimitAtZeroWithoutItsZero.ALimitAtZeroWithoutItsZero
