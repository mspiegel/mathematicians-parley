module

public import AlgebraTactics
public import ArithTactics
public import OrderTactics
public import PowerTactics
public import RealTactics
public import SetTactics
public import SubstTactics
public import Tactics
public import Parley.Items.Stdlib.Calculus
public import Parley.Items.Stdlib.Functions
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/hammack/sign-has-no-limit.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.SignHasNoLimit.SignHasNoLimit

set_option maxHeartbeats 600000 in
theorem sign_has_no_limit (f : ℝ → ℝ) (hH1 : Set.MapsTo f ((Set.univ : Set ℝ) \ ({(0 : ℝ)} : Set ℝ)) (Set.univ : Set ℝ)) (hH2 : ∀ x ∈ (Set.univ : Set ℝ) \ ({(0 : ℝ)} : Set ℝ), f x = abs x / x) :
    ¬ (∃ L : ℝ, Filter.Tendsto f (nhdsWithin 0 (((Set.univ : Set ℝ) \ ({(0 : ℝ)} : Set ℝ)) \ {0})) (nhds L)) := by
  -- the theorem. contradiction
  have sThm : ¬ (∃ L : ℝ, Filter.Tendsto f (nhdsWithin 0 (((Set.univ : Set ℝ) \ ({(0 : ℝ)} : Set ℝ)) \ {0})) (nhds L)) := by
    by_contra hc_hS
    have hS : ∃ L : ℝ, Filter.Tendsto f (nhdsWithin 0 (((Set.univ : Set ℝ) \ ({(0 : ℝ)} : Set ℝ)) \ {0})) (nhds L) := by parley_suppose hc_hS
    -- 1. obtain L from S
    obtain ⟨L, s1⟩ := hS
    -- 2. def:limit-at D := ℝ ∖ {0}, c := 0, from 1
    have r24_1 : (Set.univ : Set ℝ) \ ({(0 : ℝ)} : Set ℝ) ⊆ (Set.univ : Set ℝ) := by first | exact (Parley.Items.Stdlib.Sets.mun_difference_subset (X := (Set.univ : Set ℝ)) (Y := ({(0 : ℝ)} : Set ℝ))) | exact ((Parley.Items.Stdlib.Sets.mun_difference_subset (X := (Set.univ : Set ℝ)) (Y := ({(0 : ℝ)} : Set ℝ)))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_difference_subset (X := (Set.univ : Set ℝ)) (Y := ({(0 : ℝ)} : Set ℝ))) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_difference_subset (X := (Set.univ : Set ℝ)) (Y := ({(0 : ℝ)} : Set ℝ))) | (have h := (Parley.Items.Stdlib.Sets.mun_difference_subset (X := (Set.univ : Set ℝ)) (Y := ({(0 : ℝ)} : Set ℝ))); parley_rat_of_real h) | (have h := (Parley.Items.Stdlib.Sets.mun_difference_subset (X := (Set.univ : Set ℝ)) (Y := ({(0 : ℝ)} : Set ℝ))); parley_set_side)
    have s2 : ∀ ε : ℝ, ε > 0 → (∃ δ : ℝ, δ > 0 ∧ (∀ x ∈ (Set.univ : Set ℝ) \ ({(0 : ℝ)} : Set ℝ), x ≠ 0 ∧ abs x < δ → abs (f x - L) < ε)) := by first | exact ((Parley.Items.Stdlib.Calculus.def_limit_at (f := f) (D := (Set.univ : Set ℝ) \ ({(0 : ℝ)} : Set ℝ)) (by parley_set_side) (c := (0 : ℝ)) (L := L))).mp (by parley_set_side) | exact (((Parley.Items.Stdlib.Calculus.def_limit_at (f := f) (D := (Set.univ : Set ℝ) \ ({(0 : ℝ)} : Set ℝ)) (by parley_set_side) (c := (0 : ℝ)) (L := L))).mp (by parley_set_side)).symm | simpa using ((Parley.Items.Stdlib.Calculus.def_limit_at (f := f) (D := (Set.univ : Set ℝ) \ ({(0 : ℝ)} : Set ℝ)) (by parley_set_side) (c := (0 : ℝ)) (L := L))).mp (by parley_set_side) | exact_mod_cast ((Parley.Items.Stdlib.Calculus.def_limit_at (f := f) (D := (Set.univ : Set ℝ) \ ({(0 : ℝ)} : Set ℝ)) (by parley_set_side) (c := (0 : ℝ)) (L := L))).mp (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Calculus.def_limit_at (f := f) (D := (Set.univ : Set ℝ) \ ({(0 : ℝ)} : Set ℝ)) (by parley_set_side) (c := (0 : ℝ)) (L := L))).mp (by parley_set_side); parley_rat_of_real h) | (have h := ((Parley.Items.Stdlib.Calculus.def_limit_at (f := f) (D := (Set.univ : Set ℝ) \ ({(0 : ℝ)} : Set ℝ)) (by parley_set_side) (c := (0 : ℝ)) (L := L))).mp (by parley_set_side); parley_set_side)
    -- 3. instantiate ε := 1 in line 2
    have r28_1 : (0 : ℤ) < 1 := by parley_arith
    have s3 : ∃ δ : ℝ, δ > 0 ∧ (∀ x ∈ (Set.univ : Set ℝ) \ ({(0 : ℝ)} : Set ℝ), x ≠ 0 ∧ abs x < δ → abs (f x - L) < 1) := by first | exact (s2 (1 : ℝ) (by parley_set_side)) | exact ((s2 (1 : ℝ) (by parley_set_side))).symm | simpa using (s2 (1 : ℝ) (by parley_set_side)) | exact_mod_cast (s2 (1 : ℝ) (by parley_set_side)) | (have h := (s2 (1 : ℝ) (by parley_set_side)); parley_rat_of_real h) | (have h := (s2 (1 : ℝ) (by parley_set_side)); parley_set_side)
    -- 4. obtain p from line 3
    obtain ⟨p, ⟨s4a, s4b⟩⟩ := s3
    -- 5. inequalities
    have s5 : p / 2 > 0 := by parley_order
    -- 6. inequalities
    have s6 : p / 2 ≠ 0 := by parley_set_side
    -- 7. mun:remove-member u := p/2, from 6
    have s7 : p / 2 ∈ (Set.univ : Set ℝ) \ ({(0 : ℝ)} : Set ℝ) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.mun_remove_member (Y := (Set.univ : Set ℝ)) (a := (0 : ℝ)) (u := p / 2))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.mun_remove_member (Y := (Set.univ : Set ℝ)) (a := (0 : ℝ)) (u := p / 2))).mpr (by parley_set_side); parley_set_side)
    -- 8. def:abs x := p/2
    have r48_1 : p / 2 ≥ 0 := by parley_set_side
    have s8 : abs (p / 2) = p / 2 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.def_abs_1 (x := p / 2)) (by parley_set_side) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_1 (x := p / 2)) (by parley_set_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_1 (x := p / 2)) (by parley_set_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.def_abs_1 (x := p / 2)) (by parley_set_side) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.def_abs_1 (x := p / 2)) (by parley_set_side)).symm | (have h := (Parley.Items.Stdlib.Numbers.def_abs_1 (x := p / 2)) (by parley_set_side); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_1 (x := p / 2)) (by parley_set_side); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_1 (x := p / 2)) (by parley_set_side); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_1 (x := p / 2)) (by parley_set_side); parley_set_side)
    -- 9. inequalities
    have s9 : p / 2 < p := by parley_order
    -- 10. transitivity, from 8, 9
    have s10 : abs (p / 2) < p := by parley_order
    -- 11. instantiate x := p/2 in line 4, from 6, 7, 10
    have s11 : abs (f (p / 2) - L) < 1 := by first | linarith [(s4b (p / 2) (by parley_set_side) (by parley_set_side))] | (have h := (s4b (p / 2) (by parley_set_side) (by parley_set_side)); push_cast at h; linarith) | exact_mod_cast (s4b (p / 2) (by parley_set_side) (by parley_set_side)) | (have h := (s4b (p / 2) (by parley_set_side) (by parley_set_side)); parley_set_side)
    -- 12. calculation
    have r65_1 : p / 2 ≠ 0 := by parley_set_side
    have s12 : f (p / 2) = 1 := by
      calc f (p / 2) = abs (p / 2) / (p / 2) := by first | linear_combination (norm := parley_norm) (hH2 (p / 2) (by parley_set_side)) | (have h := (hH2 (p / 2) (by parley_set_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (hH2 (p / 2) (by parley_set_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (hH2 (p / 2) (by parley_set_side)) | exact_mod_cast ((hH2 (p / 2) (by parley_set_side))).symm | (have h := (hH2 (p / 2) (by parley_set_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (hH2 (p / 2) (by parley_set_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (hH2 (p / 2) (by parley_set_side)); parley_int_power h) | (have h := (hH2 (p / 2) (by parley_set_side)); parley_set_side)
        _ = 1 := by linear_combination (norm := parley_field) ((4) / ((p) * (2))) * s8
    -- 13. mun:abs-difference-lt x := f(p/2), c := L, δ := 1, from 11
    have s13 : f (p / 2) < L + 1 := by first | linarith [(((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := f (p / 2)) (c := L) (δ := (1 : ℝ)))).mp (by parley_set_side)).2] | (have h := (((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := f (p / 2)) (c := L) (δ := (1 : ℝ)))).mp (by parley_set_side)).2; push_cast at h; linarith) | exact_mod_cast (((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := f (p / 2)) (c := L) (δ := (1 : ℝ)))).mp (by parley_set_side)).2 | (have h := (((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := f (p / 2)) (c := L) (δ := (1 : ℝ)))).mp (by parley_set_side)).2; parley_set_side)
    -- 14. transitivity, from 12, 13
    have s14 : 1 < L + 1 := by parley_order
    -- 15. inequalities
    have s15 : 0 < L := by parley_order
    -- 16. inequalities
    have s16 : -p / 2 ≠ 0 := by parley_set_side
    -- 17. mun:remove-member u := (−p)/2, from 16
    have s17 : -p / 2 ∈ (Set.univ : Set ℝ) \ ({(0 : ℝ)} : Set ℝ) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.mun_remove_member (Y := (Set.univ : Set ℝ)) (a := (0 : ℝ)) (u := -p / 2))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.mun_remove_member (Y := (Set.univ : Set ℝ)) (a := (0 : ℝ)) (u := -p / 2))).mpr (by parley_set_side); parley_set_side)
    -- 18. mun:abs-negative x := p/2
    have s18 : abs (-(p / 2)) = abs (p / 2) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_abs_negative (x := p / 2)) | (have h := (Parley.Items.Stdlib.Numbers.mun_abs_negative (x := p / 2)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_abs_negative (x := p / 2)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_abs_negative (x := p / 2)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_abs_negative (x := p / 2))).symm | (have h := (Parley.Items.Stdlib.Numbers.mun_abs_negative (x := p / 2)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_abs_negative (x := p / 2)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_abs_negative (x := p / 2)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.mun_abs_negative (x := p / 2)); parley_set_side)
    -- 19. substitute
    have s19 : abs (-p / 2) = abs (p / 2) := by
      have c1 : -(p / 2) = -p / 2 := by parley_ring
      have row1 : abs (-p / 2) = abs (p / 2) := by parley_subst_at c1 s18
      exact row1
    -- 20. transitivity, from 19, 8, 9
    have s20 : abs (-p / 2) < p := by parley_order
    -- 21. instantiate x := (−p)/2 in line 4, from 16, 17, 20
    have s21 : abs (f (-p / 2) - L) < 1 := by first | linarith [(s4b (-p / 2) (by parley_set_side) (by parley_set_side))] | (have h := (s4b (-p / 2) (by parley_set_side) (by parley_set_side)); push_cast at h; linarith) | exact_mod_cast (s4b (-p / 2) (by parley_set_side) (by parley_set_side)) | (have h := (s4b (-p / 2) (by parley_set_side) (by parley_set_side)); parley_set_side)
    -- 22. calculation
    have r106_1 : -p / 2 ≠ 0 := by parley_set_side
    have s22 : f (-p / 2) = -1 := by
      calc f (-p / 2) = abs (-p / 2) / (-p / 2) := by first | linear_combination (norm := parley_norm) (hH2 (-p / 2) (by parley_set_side)) | (have h := (hH2 (-p / 2) (by parley_set_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (hH2 (-p / 2) (by parley_set_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (hH2 (-p / 2) (by parley_set_side)) | exact_mod_cast ((hH2 (-p / 2) (by parley_set_side))).symm | (have h := (hH2 (-p / 2) (by parley_set_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (hH2 (-p / 2) (by parley_set_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (hH2 (-p / 2) (by parley_set_side)); parley_int_power h) | (have h := (hH2 (-p / 2) (by parley_set_side)); parley_set_side)
        _ = -1 := by linear_combination (norm := parley_field) ((4) / ((-p) * (2))) * s8 + ((2) / ((-p))) * s19
    -- 23. mun:abs-difference-lt x := f((−p)/2), c := L, δ := 1, from 21
    have s23 : L - 1 < f (-p / 2) := by first | linarith [(((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := f (-p / 2)) (c := L) (δ := (1 : ℝ)))).mp (by parley_set_side)).1] | (have h := (((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := f (-p / 2)) (c := L) (δ := (1 : ℝ)))).mp (by parley_set_side)).1; push_cast at h; linarith) | exact_mod_cast (((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := f (-p / 2)) (c := L) (δ := (1 : ℝ)))).mp (by parley_set_side)).1 | (have h := (((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := f (-p / 2)) (c := L) (δ := (1 : ℝ)))).mp (by parley_set_side)).1; parley_set_side)
    -- 24. transitivity, from 23, 22
    have s24 : L - 1 < -1 := by parley_order
    -- 25. inequalities
    have s25 : L < 0 := by parley_order
    -- 26. inequalities
    have s26 : L ≤ 0 := by parley_order
    -- 27. inequalities, from 26
    have s27 : ¬ 0 < L := by parley_set_side
    all_goals parley_set_side
  all_goals parley_set_side

end Parley.Proofs.Hammack.SignHasNoLimit.SignHasNoLimit
