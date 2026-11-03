module

public import Tactics
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/setmm/whole-number-by-size.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.WholeNumberBySize.WholeNumberBySize

theorem whole_number_by_size (A : ℝ) :
    ((∃ m : ℤ, (m : ℝ) = A) ↔ (∃ m : ℤ, (m : ℝ) = abs A)) := by
  -- the theorem. both directions
  have sThm : (∃ m : ℤ, (m : ℝ) = A) ↔ (∃ m : ℤ, (m : ℝ) = abs A) := by
    constructor
    · skip
      intro hD1
      -- 1. mun:abs-integer z := A, from D1
      have s1 : ∃ m : ℕ, (m : ℝ) = abs A := by (exact ⟨(abs (Classical.choose hD1)).toNat, by rw [show (((abs (Classical.choose hD1)).toNat : ℕ) : ℝ) = (((abs (Classical.choose hD1)) : ℤ) : ℝ) by exact_mod_cast Int.toNat_of_nonneg (by parley_side)]; push_cast; (try simp only [Classical.choose_spec hD1]); first | done | parley_ring⟩)
      -- 2. mun:nat0-int m := |A|, from 1
      have s2 : ∃ m : ℤ, (m : ℝ) = abs A := by (exact ⟨abs (Classical.choose hD1), by push_cast; (try simp only [Classical.choose_spec hD1]); first | done | parley_ring⟩)
      all_goals parley_side
    · skip
      intro hD2
      -- 3. mun:nonneg-or-neg x := A
      have s3 : A ≥ 0 ∨ A < 0 := by first | exact (Parley.Items.Stdlib.Numbers.mun_nonneg_or_neg (x := A)) | exact ((Parley.Items.Stdlib.Numbers.mun_nonneg_or_neg (x := A))).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_nonneg_or_neg (x := A)) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_nonneg_or_neg (x := A)) | (have h := (Parley.Items.Stdlib.Numbers.mun_nonneg_or_neg (x := A)); parley_side)
      -- 4. cases, from 3
      have s4 : ∃ m : ℤ, (m : ℝ) = A := by
        rcases s3 with hC1 | hC2
        · skip
          -- 4.1. def:abs x := A, from C1
          have s4_1 : abs A = A := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.def_abs_1 (x := A)) (by parley_side) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_1 (x := A)) (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_1 (x := A)) (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.def_abs_1 (x := A)) (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.def_abs_1 (x := A)) (by parley_side)).symm | (have h := (Parley.Items.Stdlib.Numbers.def_abs_1 (x := A)) (by parley_side); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_1 (x := A)) (by parley_side); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_1 (x := A)) (by parley_side); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_1 (x := A)) (by parley_side); parley_side)
          -- 4.2. substitute |A| = A (line 4.1) into D2
          have s4_2 : ∃ m : ℤ, (m : ℝ) = A := by parley_subst_at s4_1 hD2
          all_goals parley_side
        · skip
          -- 4.3. def:abs x := A, from C2
          have s4_3 : abs A = -A := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.def_abs_2 (x := A)) (by parley_side) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_2 (x := A)) (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_2 (x := A)) (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.def_abs_2 (x := A)) (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.def_abs_2 (x := A)) (by parley_side)).symm | (have h := (Parley.Items.Stdlib.Numbers.def_abs_2 (x := A)) (by parley_side); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_2 (x := A)) (by parley_side); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_2 (x := A)) (by parley_side); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_2 (x := A)) (by parley_side); parley_side)
          -- 4.4. substitute |A| = −A (line 4.3) into D2
          have s4_4 : ∃ m : ℤ, (m : ℝ) = -A := by parley_subst_at s4_3 hD2
          -- 4.5. membership, from 4.4
          have s4_5 : ∃ m : ℤ, (m : ℝ) = 0 - -A := by (exact ⟨0 - (Classical.choose s4_4), by push_cast; (try simp only [Classical.choose_spec s4_4]); first | done | parley_ring⟩)
          -- 4.6. substitute
          have s4_6 : ∃ m : ℤ, (m : ℝ) = A := by
            have c1 : 0 - -A = A := by parley_ring
            have row1 : ∃ m : ℤ, (m : ℝ) = A := by parley_subst_at c1 s4_5
            exact row1
          all_goals parley_side
      all_goals parley_side
  all_goals parley_side

end Parley.Proofs.Setmm.WholeNumberBySize.WholeNumberBySize
