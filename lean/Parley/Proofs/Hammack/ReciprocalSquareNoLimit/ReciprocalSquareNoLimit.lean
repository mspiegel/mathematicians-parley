module

public import AlgebraTactics
public import ArithTactics
public import OrderTactics
public import PowerTactics
public import SetTactics
public import SubstTactics
public import Tactics
public import Parley.Items.Stdlib.Calculus
public import Parley.Items.Stdlib.Functions
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/hammack/reciprocal-square-no-limit.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.ReciprocalSquareNoLimit.ReciprocalSquareNoLimit

set_option maxHeartbeats 400000 in
theorem reciprocal_square_no_limit (f : ℝ → ℝ) (hH1 : Set.MapsTo f ((Set.univ : Set ℝ) \ ({(1 : ℝ)} : Set ℝ)) (Set.univ : Set ℝ)) (hH2 : ∀ x ∈ (Set.univ : Set ℝ) \ ({(1 : ℝ)} : Set ℝ), f x = 1 / (x ^ 2 - 2 * x + 1)) :
    ¬ (∃ L : ℝ, Filter.Tendsto f (nhdsWithin 1 (((Set.univ : Set ℝ) \ ({(1 : ℝ)} : Set ℝ)) \ {1})) (nhds L)) := by
  -- the theorem. contradiction
  have sThm : ¬ (∃ L : ℝ, Filter.Tendsto f (nhdsWithin 1 (((Set.univ : Set ℝ) \ ({(1 : ℝ)} : Set ℝ)) \ {1})) (nhds L)) := by
    by_contra hc_hS
    have hS : ∃ L : ℝ, Filter.Tendsto f (nhdsWithin 1 (((Set.univ : Set ℝ) \ ({(1 : ℝ)} : Set ℝ)) \ {1})) (nhds L) := by parley_suppose hc_hS
    -- 1. obtain L from S
    obtain ⟨L, s1⟩ := hS
    -- 2. def:limit-at D := ℝ ∖ {1}, c := 1, from 1
    have r33_1 : (Set.univ : Set ℝ) \ ({(1 : ℝ)} : Set ℝ) ⊆ (Set.univ : Set ℝ) := by first | exact (Parley.Items.Stdlib.Sets.mun_difference_subset (X := (Set.univ : Set ℝ)) (Y := ({(1 : ℝ)} : Set ℝ))) | exact ((Parley.Items.Stdlib.Sets.mun_difference_subset (X := (Set.univ : Set ℝ)) (Y := ({(1 : ℝ)} : Set ℝ)))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_difference_subset (X := (Set.univ : Set ℝ)) (Y := ({(1 : ℝ)} : Set ℝ))) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_difference_subset (X := (Set.univ : Set ℝ)) (Y := ({(1 : ℝ)} : Set ℝ))) | (have h := (Parley.Items.Stdlib.Sets.mun_difference_subset (X := (Set.univ : Set ℝ)) (Y := ({(1 : ℝ)} : Set ℝ))); parley_set_side)
    have s2 : ∀ ε : ℝ, ε > 0 → (∃ δ : ℝ, δ > 0 ∧ (∀ x ∈ (Set.univ : Set ℝ) \ ({(1 : ℝ)} : Set ℝ), x ≠ 1 ∧ abs (x - 1) < δ → abs (f x - L) < ε)) := by first | exact ((Parley.Items.Stdlib.Calculus.def_limit_at (f := f) (D := (Set.univ : Set ℝ) \ ({(1 : ℝ)} : Set ℝ)) (by parley_set_side) (c := (1 : ℝ)) (L := L) (by parley_set_side))).mp (by parley_set_side) | exact (((Parley.Items.Stdlib.Calculus.def_limit_at (f := f) (D := (Set.univ : Set ℝ) \ ({(1 : ℝ)} : Set ℝ)) (by parley_set_side) (c := (1 : ℝ)) (L := L) (by parley_set_side))).mp (by parley_set_side)).symm | simpa using ((Parley.Items.Stdlib.Calculus.def_limit_at (f := f) (D := (Set.univ : Set ℝ) \ ({(1 : ℝ)} : Set ℝ)) (by parley_set_side) (c := (1 : ℝ)) (L := L) (by parley_set_side))).mp (by parley_set_side) | exact_mod_cast ((Parley.Items.Stdlib.Calculus.def_limit_at (f := f) (D := (Set.univ : Set ℝ) \ ({(1 : ℝ)} : Set ℝ)) (by parley_set_side) (c := (1 : ℝ)) (L := L) (by parley_set_side))).mp (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Calculus.def_limit_at (f := f) (D := (Set.univ : Set ℝ) \ ({(1 : ℝ)} : Set ℝ)) (by parley_set_side) (c := (1 : ℝ)) (L := L) (by parley_set_side))).mp (by parley_set_side); parley_set_side)
    -- 3. instantiate ε := 1 in line 2
    have r37_1 : (0 : ℝ) < 1 := by parley_arith
    have s3 : ∃ δ : ℝ, δ > 0 ∧ (∀ x ∈ (Set.univ : Set ℝ) \ ({(1 : ℝ)} : Set ℝ), x ≠ 1 ∧ abs (x - 1) < δ → abs (f x - L) < 1) := by first | exact (s2 (1 : ℝ) (by parley_set_side)) | exact ((s2 (1 : ℝ) (by parley_set_side))).symm | simpa using (s2 (1 : ℝ) (by parley_set_side)) | exact_mod_cast (s2 (1 : ℝ) (by parley_set_side)) | (have h := (s2 (1 : ℝ) (by parley_set_side)); parley_set_side)
    -- 4. obtain p from line 3
    obtain ⟨p, ⟨s4a, s4b⟩⟩ := s3
    -- 5. inequalities
    have s5 : p ≠ 0 := by parley_set_side
    -- 6. mun:reciprocal-positive x := p, from 4
    have s6 : 1 / p > 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_reciprocal_positive (x := p) (by parley_set_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_reciprocal_positive (x := p) (by parley_set_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_reciprocal_positive (x := p) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_reciprocal_positive (x := p) (by parley_set_side)); parley_set_side)
    -- 7. mun:quotient-real x := 1, y := p, from 5
    -- 8. mun:max-real x := 1/p, y := L + 1, from 7
    -- 9. obtain N: thm:archimedean-natural x := max(1/p, L + 1), from 8
    obtain ⟨N, s9a, s9b⟩ := (Parley.Items.Stdlib.Numbers.thm_archimedean_natural (x := max (1 / p) (L + 1)))
    -- 10. mun:le-max x := 1/p, y := L + 1, from 7
    have s10 : 1 / p ≤ max (1 / p) (L + 1) := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_le_max_1 (x := 1 / p) (y := L + 1))] | (have h := (Parley.Items.Stdlib.Numbers.mun_le_max_1 (x := 1 / p) (y := L + 1)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_le_max_1 (x := 1 / p) (y := L + 1)) | (have h := (Parley.Items.Stdlib.Numbers.mun_le_max_1 (x := 1 / p) (y := L + 1)); parley_set_side)
    -- 11. mun:le-max x := 1/p, y := L + 1, from 7
    have s11 : L + 1 ≤ max (1 / p) (L + 1) := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_le_max_2 (x := 1 / p) (y := L + 1))] | (have h := (Parley.Items.Stdlib.Numbers.mun_le_max_2 (x := 1 / p) (y := L + 1)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_le_max_2 (x := 1 / p) (y := L + 1)) | (have h := (Parley.Items.Stdlib.Numbers.mun_le_max_2 (x := 1 / p) (y := L + 1)); parley_set_side)
    -- 12. transitivity, from 10, 9
    have r67_1 : p ≠ 0 := by parley_set_side
    have s12 : 1 / p < (N : ℝ) := by parley_order
    -- 13. transitivity, from 11, 9
    have s13 : L + 1 < (N : ℝ) := by parley_order
    -- 14. inequalities, from 9
    have s14 : (N : ℝ) > 0 := by parley_order
    -- 15. mun:reciprocal-positive x := N, from 14
    have s15 : 1 / (N : ℝ) > 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_reciprocal_positive (x := (N : ℝ)) (by parley_set_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_reciprocal_positive (x := (N : ℝ)) (by parley_set_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_reciprocal_positive (x := (N : ℝ)) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_reciprocal_positive (x := (N : ℝ)) (by parley_set_side)); parley_set_side)
    -- 16. inequalities
    have s16 : 1 + 1 / (N : ℝ) ≠ 1 := by parley_set_side
    -- 17. mun:remove-member u := 1 + 1/N, from 16
    have s17 : 1 + 1 / (N : ℝ) ∈ (Set.univ : Set ℝ) \ ({(1 : ℝ)} : Set ℝ) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.mun_remove_member (Y := (Set.univ : Set ℝ)) (a := (1 : ℝ)) (u := 1 + 1 / (N : ℝ)))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.mun_remove_member (Y := (Set.univ : Set ℝ)) (a := (1 : ℝ)) (u := 1 + 1 / (N : ℝ)))).mpr (by parley_set_side); parley_set_side)
    -- 18. mun:reciprocal-order-strict x := 1/p, y := N, from 6, 7, 12, 14
    have s18 : 1 / (N : ℝ) < 1 / (1 / p) := by first | linarith [((Parley.Items.Stdlib.Numbers.mun_reciprocal_order_strict (x := 1 / p) (by parley_set_side) (y := (N : ℝ)) (by parley_set_side))).mp (by parley_set_side)] | (have h := ((Parley.Items.Stdlib.Numbers.mun_reciprocal_order_strict (x := 1 / p) (by parley_set_side) (y := (N : ℝ)) (by parley_set_side))).mp (by parley_set_side); push_cast at h; linarith) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_reciprocal_order_strict (x := 1 / p) (by parley_set_side) (y := (N : ℝ)) (by parley_set_side))).mp (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_reciprocal_order_strict (x := 1 / p) (by parley_set_side) (y := (N : ℝ)) (by parley_set_side))).mp (by parley_set_side); parley_set_side)
    -- 19. substitute
    have r94_1 : p ≠ 0 := by parley_set_side
    have s19 : 1 / (N : ℝ) < p := by
      have c1 : 1 / (1 / p) = p := by parley_ring
      have row1 : 1 / (N : ℝ) < p := by parley_subst_at c1 s18
      exact row1
    -- 20. algebra
    have s20 : 1 + 1 / (N : ℝ) - 1 = 1 / (N : ℝ) := by parley_ring
    -- 21. calculation
    have r103_1 : 1 / (N : ℝ) ≥ 0 := by parley_set_side
    have s21 : abs (1 + 1 / (N : ℝ) - 1) < p := by
      calc abs (1 + 1 / (N : ℝ) - 1) = abs (1 / (N : ℝ)) := by parley_subst s20
        _ = 1 / (N : ℝ) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.def_abs_1 (x := 1 / (N : ℝ))) (by parley_set_side) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_1 (x := 1 / (N : ℝ))) (by parley_set_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_1 (x := 1 / (N : ℝ))) (by parley_set_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.def_abs_1 (x := 1 / (N : ℝ))) (by parley_set_side) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.def_abs_1 (x := 1 / (N : ℝ))) (by parley_set_side)).symm | (have h := (Parley.Items.Stdlib.Numbers.def_abs_1 (x := 1 / (N : ℝ))) (by parley_set_side); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_1 (x := 1 / (N : ℝ))) (by parley_set_side); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_1 (x := 1 / (N : ℝ))) (by parley_set_side); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_1 (x := 1 / (N : ℝ))) (by parley_set_side); parley_set_side)
        _ < p := by parley_set_side
    -- 22. join 16, 21
    have s22 : 1 + 1 / (N : ℝ) ≠ 1 ∧ abs (1 + 1 / (N : ℝ) - 1) < p := by parley_set_side
    -- 23. instantiate x := 1 + 1/N in line 4, from 17, 22
    have s23 : abs (f (1 + 1 / (N : ℝ)) - L) < 1 := by first | linarith [(s4b (1 + 1 / (N : ℝ)) (by parley_set_side) (by parley_set_side))] | (have h := (s4b (1 + 1 / (N : ℝ)) (by parley_set_side) (by parley_set_side)); push_cast at h; linarith) | exact_mod_cast (s4b (1 + 1 / (N : ℝ)) (by parley_set_side) (by parley_set_side)) | (have h := (s4b (1 + 1 / (N : ℝ)) (by parley_set_side) (by parley_set_side)); parley_set_side)
    -- 24. inequalities
    have s24 : 1 / (N : ℝ) ≠ 0 := by parley_set_side
    -- 25. mun:square-positive x := 1/N, from 24
    have s25 : (1 / (N : ℝ)) ^ 2 > 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_square_positive (x := 1 / (N : ℝ)) (by parley_set_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_square_positive (x := 1 / (N : ℝ)) (by parley_set_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_square_positive (x := 1 / (N : ℝ)) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_square_positive (x := 1 / (N : ℝ)) (by parley_set_side)); parley_set_side)
    -- 26. substitute
    have s26 : (1 + 1 / (N : ℝ)) ^ 2 - 2 * (1 + 1 / (N : ℝ)) + 1 > 0 := by
      have c1 : (1 / (N : ℝ)) ^ 2 = (1 + 1 / (N : ℝ)) ^ 2 - 2 * (1 + 1 / (N : ℝ)) + 1 := by parley_ring
      have row1 : (1 + 1 / (N : ℝ)) ^ 2 - 2 * (1 + 1 / (N : ℝ)) + 1 > 0 := by parley_subst_at c1 s25
      exact row1
    -- 27. inequalities
    have s27 : (1 + 1 / (N : ℝ)) ^ 2 - 2 * (1 + 1 / (N : ℝ)) + 1 ≠ 0 := by parley_set_side
    -- 28. calculation
    have s28 : f (1 + 1 / (N : ℝ)) = (N : ℝ) ^ 2 := by
      calc f (1 + 1 / (N : ℝ)) = 1 / ((1 + 1 / (N : ℝ)) ^ 2 - 2 * (1 + 1 / (N : ℝ)) + 1) := by first | linear_combination (norm := parley_norm) (hH2 (1 + 1 / (N : ℝ)) (by parley_set_side)) | (have h := (hH2 (1 + 1 / (N : ℝ)) (by parley_set_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (hH2 (1 + 1 / (N : ℝ)) (by parley_set_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (hH2 (1 + 1 / (N : ℝ)) (by parley_set_side)) | exact_mod_cast ((hH2 (1 + 1 / (N : ℝ)) (by parley_set_side))).symm | (have h := (hH2 (1 + 1 / (N : ℝ)) (by parley_set_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (hH2 (1 + 1 / (N : ℝ)) (by parley_set_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (hH2 (1 + 1 / (N : ℝ)) (by parley_set_side)); parley_int_power h) | (have h := (hH2 (1 + 1 / (N : ℝ)) (by parley_set_side)); parley_set_side)
        _ = (N : ℝ) ^ 2 := by parley_ring
    -- 29. mun:abs-difference-lt x := f(1 + 1/N), c := L, δ := 1, from 23
    have s29 : L - 1 < f (1 + 1 / (N : ℝ)) ∧ f (1 + 1 / (N : ℝ)) < L + 1 := by first | exact ((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := f (1 + 1 / (N : ℝ))) (c := L) (δ := (1 : ℝ)))).mp (by parley_set_side) | exact (((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := f (1 + 1 / (N : ℝ))) (c := L) (δ := (1 : ℝ)))).mp (by parley_set_side)).symm | simpa using ((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := f (1 + 1 / (N : ℝ))) (c := L) (δ := (1 : ℝ)))).mp (by parley_set_side) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := f (1 + 1 / (N : ℝ))) (c := L) (δ := (1 : ℝ)))).mp (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := f (1 + 1 / (N : ℝ))) (c := L) (δ := (1 : ℝ)))).mp (by parley_set_side); parley_set_side)
    -- 30. substitute f(1 + 1/N) = N² (line 28) into line 29
    have s30 : (N : ℝ) ^ 2 < L + 1 := by parley_subst_at s28 s29
    -- 31. mun:multiply-le x := 1, y := N, c := N, from 9
    have s31 : (N : ℝ) * 1 ≤ (N : ℝ) * (N : ℝ) := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_multiply_le (x := (1 : ℝ)) (y := (N : ℝ)) (c := (N : ℝ)) (by parley_set_side) (by parley_set_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_le (x := (1 : ℝ)) (y := (N : ℝ)) (c := (N : ℝ)) (by parley_set_side) (by parley_set_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_multiply_le (x := (1 : ℝ)) (y := (N : ℝ)) (c := (N : ℝ)) (by parley_set_side) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_le (x := (1 : ℝ)) (y := (N : ℝ)) (c := (N : ℝ)) (by parley_set_side) (by parley_set_side)); parley_set_side)
    -- 32. inequalities
    have s32 : (N : ℝ) ≤ (N : ℝ) ^ 2 := by parley_order
    -- 33. transitivity, from 13, 32
    have s33 : L + 1 < (N : ℝ) ^ 2 := by parley_order
    -- 34. inequalities
    have s34 : L + 1 ≤ (N : ℝ) ^ 2 := by parley_order
    -- 35. inequalities, from 34
    have s35 : ¬ (N : ℝ) ^ 2 < L + 1 := by parley_set_side
    all_goals parley_set_side
  all_goals parley_set_side

end Parley.Proofs.Hammack.ReciprocalSquareNoLimit.ReciprocalSquareNoLimit
