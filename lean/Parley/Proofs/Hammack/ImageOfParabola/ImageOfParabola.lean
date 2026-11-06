module

public import ArithTactics
public import OrderTactics
public import PowerTactics
public import RealTactics
public import SetTactics
public import SubstTactics
public import Tactics
public import WholeTactics
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.SetNotationForOrder
public import Parley.Items.Stdlib.Calculus
public import Parley.Items.Stdlib.Functions
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/hammack/image-of-parabola.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.ImageOfParabola.ImageOfParabola

set_option maxHeartbeats 800000 in
theorem image_of_parabola (f : ℝ → ℝ) (hH2 : ∀ x : ℝ, f x = x ^ 2 + 3) :
    f '' ((Set.univ : Set ℝ) ∩ (Set.Icc (-3 : ℝ) (5 : ℝ) : Set ℝ)) = (Set.Icc (3 : ℝ) (28 : ℝ) : Set ℝ) := by
  -- 1. mun:interval-real a := −3, b := 5
  have s1 : (Set.Icc (-3 : ℝ) (5 : ℝ) : Set ℝ) ⊆ (Set.univ : Set ℝ) := by first | exact (Parley.Items.Stdlib.Calculus.mun_interval_real (a := (-3 : ℝ)) (b := (5 : ℝ))) | exact ((Parley.Items.Stdlib.Calculus.mun_interval_real (a := (-3 : ℝ)) (b := (5 : ℝ)))).symm | simpa using (Parley.Items.Stdlib.Calculus.mun_interval_real (a := (-3 : ℝ)) (b := (5 : ℝ))) | exact_mod_cast (Parley.Items.Stdlib.Calculus.mun_interval_real (a := (-3 : ℝ)) (b := (5 : ℝ))) | (have h := (Parley.Items.Stdlib.Calculus.mun_interval_real (a := (-3 : ℝ)) (b := (5 : ℝ))); parley_rat_of_real h) | (have h := (Parley.Items.Stdlib.Calculus.mun_interval_real (a := (-3 : ℝ)) (b := (5 : ℝ))); parley_set_side)
  -- 2. proof
  have s2 : ∀ y ∈ f '' ((Set.univ : Set ℝ) ∩ (Set.Icc (-3 : ℝ) (5 : ℝ) : Set ℝ)), y ∈ (Set.Icc (3 : ℝ) (28 : ℝ) : Set ℝ) := by
    intro y hK1
    -- 2.1. obtain s: def:image u := y, Y := [−3, 5], from K1, 1
    obtain ⟨s, s2_1a, s2_1b⟩ := ((Parley.Items.Stdlib.Functions.def_image (X := (Set.univ : Set ℝ)) (Y := (Set.Icc (-3 : ℝ) (5 : ℝ) : Set ℝ)) (f := f) (u := y) (W := Set.univ) (by parley_whole_side) (by parley_whole_side))).mp (by parley_set_side)
    -- 2.2. def:interval a := −3, b := 5, x := s, from 2.1
    have s2_2a : -3 ≤ s := by first | linarith [(((Parley.Items.Stdlib.Calculus.def_interval (x := s) (a := (-3 : ℝ)) (b := (5 : ℝ)))).mp (by parley_set_side)).1.2] | (have h := (((Parley.Items.Stdlib.Calculus.def_interval (x := s) (a := (-3 : ℝ)) (b := (5 : ℝ)))).mp (by parley_set_side)).1.2; push_cast at h; linarith) | exact_mod_cast (((Parley.Items.Stdlib.Calculus.def_interval (x := s) (a := (-3 : ℝ)) (b := (5 : ℝ)))).mp (by parley_set_side)).1.2 | (have h := (((Parley.Items.Stdlib.Calculus.def_interval (x := s) (a := (-3 : ℝ)) (b := (5 : ℝ)))).mp (by parley_set_side)).1.2; parley_set_side)
    have s2_2b : s ≤ 5 := by first | linarith [(((Parley.Items.Stdlib.Calculus.def_interval (x := s) (a := (-3 : ℝ)) (b := (5 : ℝ)))).mp (by parley_set_side)).2] | (have h := (((Parley.Items.Stdlib.Calculus.def_interval (x := s) (a := (-3 : ℝ)) (b := (5 : ℝ)))).mp (by parley_set_side)).2; push_cast at h; linarith) | exact_mod_cast (((Parley.Items.Stdlib.Calculus.def_interval (x := s) (a := (-3 : ℝ)) (b := (5 : ℝ)))).mp (by parley_set_side)).2 | (have h := (((Parley.Items.Stdlib.Calculus.def_interval (x := s) (a := (-3 : ℝ)) (b := (5 : ℝ)))).mp (by parley_set_side)).2; parley_set_side)
    -- 2.3. calculation
    have s2_3 : y = s ^ 2 + 3 := by
      calc y = f s := by parley_set_side
        _ = s ^ 2 + 3 := by first | linear_combination (norm := parley_norm) (hH2 s) | (have h := (hH2 s); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (hH2 s); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (hH2 s) | exact_mod_cast ((hH2 s)).symm | (have h := (hH2 s); rify; linear_combination (norm := parley_norm) h) | (have h := (hH2 s); qify; linear_combination (norm := parley_norm) h) | (have h := (hH2 s); parley_int_power h) | (have h := (hH2 s); parley_set_side)
    -- 2.4. mun:square-nonneg x := s
    have s2_4 : s ^ 2 ≥ 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := s))] | (have h := (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := s)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := s)) | (have h := (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := s)); parley_set_side)
    -- 2.5. inequalities
    have s2_5 : s ^ 2 + 3 ≥ 3 := by parley_order
    -- 2.6. calculation
    have s2_6 : y ≥ 3 := by
      calc y = s ^ 2 + 3 := by parley_set_side
        _ ≥ 3 := by parley_set_side
    -- 2.7. inequalities
    have s2_7 : s + 3 ≥ 0 := by parley_order
    -- 2.8. inequalities
    have s2_8 : 5 - s ≥ 0 := by parley_order
    -- 2.9. mun:product-nonneg x := s + 3, y := 5 − s, from 2.7, 2.8
    have s2_9 : (s + 3) * (5 - s) ≥ 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_product_nonneg (x := s + 3) (y := 5 - s) (by parley_set_side) (by parley_set_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_product_nonneg (x := s + 3) (y := 5 - s) (by parley_set_side) (by parley_set_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_product_nonneg (x := s + 3) (y := 5 - s) (by parley_set_side) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_product_nonneg (x := s + 3) (y := 5 - s) (by parley_set_side) (by parley_set_side)); parley_set_side)
    -- 2.10. inequalities
    have s2_10 : s ^ 2 + 3 ≤ 2 * s + 18 := by parley_order
    -- 2.11. inequalities
    have s2_11 : 2 * s + 18 ≤ 28 := by parley_order
    -- 2.12. calculation
    have s2_12 : y ≤ 28 := by
      calc y = s ^ 2 + 3 := by parley_set_side
        _ ≤ 2 * s + 18 := by parley_set_side
        _ ≤ 28 := by parley_set_side
    -- 2.13. membership, from 2.3
    -- 2.14. def:interval a := 3, b := 28, x := y, from 2.6, 2.12, 2.13
    have s2_14 : y ∈ (Set.Icc (3 : ℝ) (28 : ℝ) : Set ℝ) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Calculus.def_interval (x := y) (a := (3 : ℝ)) (b := (28 : ℝ)))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Calculus.def_interval (x := y) (a := (3 : ℝ)) (b := (28 : ℝ)))).mpr (by parley_set_side); parley_set_side)
    all_goals exact s2_14
  -- 3. def:subset, from 2
  have s3 : f '' ((Set.univ : Set ℝ) ∩ (Set.Icc (-3 : ℝ) (5 : ℝ) : Set ℝ)) ⊆ (Set.Icc (3 : ℝ) (28 : ℝ) : Set ℝ) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_subset (X := f '' ((Set.univ : Set ℝ) ∩ (Set.Icc (-3 : ℝ) (5 : ℝ) : Set ℝ))) (Y := (Set.Icc (3 : ℝ) (28 : ℝ) : Set ℝ)))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := f '' ((Set.univ : Set ℝ) ∩ (Set.Icc (-3 : ℝ) (5 : ℝ) : Set ℝ))) (Y := (Set.Icc (3 : ℝ) (28 : ℝ) : Set ℝ)))).mpr (by parley_set_side); parley_set_side)
  -- 4. proof
  have s4 : ∀ y ∈ (Set.Icc (3 : ℝ) (28 : ℝ) : Set ℝ), y ∈ f '' ((Set.univ : Set ℝ) ∩ (Set.Icc (-3 : ℝ) (5 : ℝ) : Set ℝ)) := by
    intro y hK2
    -- 4.1. def:interval a := 3, b := 28, x := y, from K2
    have s4_1a : 3 ≤ y := by first | linarith [(((Parley.Items.Stdlib.Calculus.def_interval (x := y) (a := (3 : ℝ)) (b := (28 : ℝ)))).mp (by parley_set_side)).1.2] | (have h := (((Parley.Items.Stdlib.Calculus.def_interval (x := y) (a := (3 : ℝ)) (b := (28 : ℝ)))).mp (by parley_set_side)).1.2; push_cast at h; linarith) | exact_mod_cast (((Parley.Items.Stdlib.Calculus.def_interval (x := y) (a := (3 : ℝ)) (b := (28 : ℝ)))).mp (by parley_set_side)).1.2 | (have h := (((Parley.Items.Stdlib.Calculus.def_interval (x := y) (a := (3 : ℝ)) (b := (28 : ℝ)))).mp (by parley_set_side)).1.2; parley_set_side)
    have s4_1b : y ≤ 28 := by first | linarith [(((Parley.Items.Stdlib.Calculus.def_interval (x := y) (a := (3 : ℝ)) (b := (28 : ℝ)))).mp (by parley_set_side)).2] | (have h := (((Parley.Items.Stdlib.Calculus.def_interval (x := y) (a := (3 : ℝ)) (b := (28 : ℝ)))).mp (by parley_set_side)).2; push_cast at h; linarith) | exact_mod_cast (((Parley.Items.Stdlib.Calculus.def_interval (x := y) (a := (3 : ℝ)) (b := (28 : ℝ)))).mp (by parley_set_side)).2 | (have h := (((Parley.Items.Stdlib.Calculus.def_interval (x := y) (a := (3 : ℝ)) (b := (28 : ℝ)))).mp (by parley_set_side)).2; parley_set_side)
    -- 4.2. inequalities
    have s4_2 : y - 3 ≥ 0 := by parley_order
    -- 4.3. def:sqrt x := y − 3, from 4.2
    have s4_3a : Real.sqrt (y - 3) ≥ 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := y - 3) (by parley_set_side))] | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := y - 3) (by parley_set_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := y - 3) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := y - 3) (by parley_set_side)); parley_set_side)
    have s4_3b : Real.sqrt (y - 3) ^ 2 = y - 3 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := y - 3) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := y - 3) (by parley_set_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := y - 3) (by parley_set_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := y - 3) (by parley_set_side)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := y - 3) (by parley_set_side))).symm | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := y - 3) (by parley_set_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := y - 3) (by parley_set_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := y - 3) (by parley_set_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := y - 3) (by parley_set_side)); parley_set_side)
    -- 4.4. inequalities
    have s4_4 : y - 3 ≤ 25 := by parley_order
    -- 4.5. calculation
    have s4_5 : Real.sqrt (y - 3) ^ 2 ≤ 5 ^ 2 := by
      calc Real.sqrt (y - 3) ^ 2 = y - 3 := by parley_set_side
        _ ≤ 25 := by parley_set_side
        _ = 5 ^ 2 := by norm_num
    -- 4.6. mun:square-le x := √(y − 3), y := 5, from 4.3, 4.5
    have r121_1 : (0 : ℤ) ≤ 5 := by parley_arith
    have s4_6 : Real.sqrt (y - 3) ≤ 5 := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Numbers.mun_square_le (x := Real.sqrt (y - 3)) (y := (5 : ℝ)) (by parley_set_side) (by parley_set_side))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_square_le (x := Real.sqrt (y - 3)) (y := (5 : ℝ)) (by parley_set_side) (by parley_set_side))).mpr (by parley_set_side); parley_set_side)
    -- 4.7. inequalities, from 4.3
    have s4_7 : -3 ≤ Real.sqrt (y - 3) := by parley_order
    -- 4.8. def:interval a := −3, b := 5, x := √(y − 3), from 4.3, 4.6, 4.7
    have s4_8 : Real.sqrt (y - 3) ∈ (Set.Icc (-3 : ℝ) (5 : ℝ) : Set ℝ) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Calculus.def_interval (x := Real.sqrt (y - 3)) (a := (-3 : ℝ)) (b := (5 : ℝ)))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Calculus.def_interval (x := Real.sqrt (y - 3)) (a := (-3 : ℝ)) (b := (5 : ℝ)))).mpr (by parley_set_side); parley_set_side)
    -- 4.9. instantiate x := √(y − 3) in H2, from 4.3
    have s4_9 : f (Real.sqrt (y - 3)) = Real.sqrt (y - 3) ^ 2 + 3 := by first | linear_combination (norm := parley_norm) (hH2 (Real.sqrt (y - 3))) | (have h := (hH2 (Real.sqrt (y - 3))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (hH2 (Real.sqrt (y - 3))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (hH2 (Real.sqrt (y - 3))) | exact_mod_cast ((hH2 (Real.sqrt (y - 3)))).symm | (have h := (hH2 (Real.sqrt (y - 3))); rify; linear_combination (norm := parley_norm) h) | (have h := (hH2 (Real.sqrt (y - 3))); qify; linear_combination (norm := parley_norm) h) | (have h := (hH2 (Real.sqrt (y - 3))); parley_int_power h) | (have h := (hH2 (Real.sqrt (y - 3))); parley_set_side)
    -- 4.10. mun:value-in-image Y := [−3, 5], s := √(y − 3), from 1, 4.8
    have s4_10 : f (Real.sqrt (y - 3)) ∈ f '' ((Set.univ : Set ℝ) ∩ (Set.Icc (-3 : ℝ) (5 : ℝ) : Set ℝ)) := by first | exact (Parley.Items.Stdlib.Functions.mun_value_in_image (X := (Set.univ : Set ℝ)) (Y := (Set.Icc (-3 : ℝ) (5 : ℝ) : Set ℝ)) (f := f) (s := Real.sqrt (y - 3)) (W := Set.univ) (by parley_whole_side) s4_8 (by parley_whole_side)) | exact ((Parley.Items.Stdlib.Functions.mun_value_in_image (X := (Set.univ : Set ℝ)) (Y := (Set.Icc (-3 : ℝ) (5 : ℝ) : Set ℝ)) (f := f) (s := Real.sqrt (y - 3)) (W := Set.univ) (by parley_whole_side) s4_8 (by parley_whole_side))).symm | simpa using (Parley.Items.Stdlib.Functions.mun_value_in_image (X := (Set.univ : Set ℝ)) (Y := (Set.Icc (-3 : ℝ) (5 : ℝ) : Set ℝ)) (f := f) (s := Real.sqrt (y - 3)) (W := Set.univ) (by parley_whole_side) s4_8 (by parley_whole_side)) | exact_mod_cast (Parley.Items.Stdlib.Functions.mun_value_in_image (X := (Set.univ : Set ℝ)) (Y := (Set.Icc (-3 : ℝ) (5 : ℝ) : Set ℝ)) (f := f) (s := Real.sqrt (y - 3)) (W := Set.univ) (by parley_whole_side) s4_8 (by parley_whole_side)) | (have h := (Parley.Items.Stdlib.Functions.mun_value_in_image (X := (Set.univ : Set ℝ)) (Y := (Set.Icc (-3 : ℝ) (5 : ℝ) : Set ℝ)) (f := f) (s := Real.sqrt (y - 3)) (W := Set.univ) (by parley_whole_side) s4_8 (by parley_whole_side)); parley_rat_of_real h) | (have h := (Parley.Items.Stdlib.Functions.mun_value_in_image (X := (Set.univ : Set ℝ)) (Y := (Set.Icc (-3 : ℝ) (5 : ℝ) : Set ℝ)) (f := f) (s := Real.sqrt (y - 3)) (W := Set.univ) (by parley_whole_side) s4_8 (by parley_whole_side)); parley_set_side)
    -- 4.11. substitute
    have s4_11 : y ∈ f '' ((Set.univ : Set ℝ) ∩ (Set.Icc (-3 : ℝ) (5 : ℝ) : Set ℝ)) := by
      have c1 : f (Real.sqrt (y - 3)) = y := by linear_combination (norm := parley_norm) s4_3b + s4_9
      have row1 : y ∈ f '' ((Set.univ : Set ℝ) ∩ (Set.Icc (-3 : ℝ) (5 : ℝ) : Set ℝ)) := by parley_subst_at c1 s4_10
      exact row1
    all_goals exact s4_11
  -- 5. def:subset, from 4
  have s5 : (Set.Icc (3 : ℝ) (28 : ℝ) : Set ℝ) ⊆ f '' ((Set.univ : Set ℝ) ∩ (Set.Icc (-3 : ℝ) (5 : ℝ) : Set ℝ)) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_subset (X := (Set.Icc (3 : ℝ) (28 : ℝ) : Set ℝ)) (Y := f '' ((Set.univ : Set ℝ) ∩ (Set.Icc (-3 : ℝ) (5 : ℝ) : Set ℝ))))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := (Set.Icc (3 : ℝ) (28 : ℝ) : Set ℝ)) (Y := f '' ((Set.univ : Set ℝ) ∩ (Set.Icc (-3 : ℝ) (5 : ℝ) : Set ℝ))))).mpr (by parley_set_side); parley_set_side)
  -- 6. mun:subset-antisymmetric, from 3, 5
  have s6 : f '' ((Set.univ : Set ℝ) ∩ (Set.Icc (-3 : ℝ) (5 : ℝ) : Set ℝ)) = (Set.Icc (3 : ℝ) (28 : ℝ) : Set ℝ) := by first | exact (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := f '' ((Set.univ : Set ℝ) ∩ (Set.Icc (-3 : ℝ) (5 : ℝ) : Set ℝ))) (Y := (Set.Icc (3 : ℝ) (28 : ℝ) : Set ℝ)) s3 s5) | exact ((Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := f '' ((Set.univ : Set ℝ) ∩ (Set.Icc (-3 : ℝ) (5 : ℝ) : Set ℝ))) (Y := (Set.Icc (3 : ℝ) (28 : ℝ) : Set ℝ)) s3 s5)).symm | simpa using (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := f '' ((Set.univ : Set ℝ) ∩ (Set.Icc (-3 : ℝ) (5 : ℝ) : Set ℝ))) (Y := (Set.Icc (3 : ℝ) (28 : ℝ) : Set ℝ)) s3 s5) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := f '' ((Set.univ : Set ℝ) ∩ (Set.Icc (-3 : ℝ) (5 : ℝ) : Set ℝ))) (Y := (Set.Icc (3 : ℝ) (28 : ℝ) : Set ℝ)) s3 s5) | (have h := (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := f '' ((Set.univ : Set ℝ) ∩ (Set.Icc (-3 : ℝ) (5 : ℝ) : Set ℝ))) (Y := (Set.Icc (3 : ℝ) (28 : ℝ) : Set ℝ)) s3 s5); parley_rat_of_real h) | (have h := (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := f '' ((Set.univ : Set ℝ) ∩ (Set.Icc (-3 : ℝ) (5 : ℝ) : Set ℝ))) (Y := (Set.Icc (3 : ℝ) (28 : ℝ) : Set ℝ)) s3 s5); parley_set_side)
  all_goals exact s6

end Parley.Proofs.Hammack.ImageOfParabola.ImageOfParabola
