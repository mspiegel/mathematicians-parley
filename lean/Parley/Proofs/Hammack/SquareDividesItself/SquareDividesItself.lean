module

public import OrderTactics
public import PowerTactics
public import SetTactics
public import SubstTactics
public import Tactics
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Reasoning

/-! Written from proofs/hammack/square-divides-itself.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.SquareDividesItself.SquareDividesItself

set_option maxHeartbeats 400000 in
theorem square_divides_itself (a : ℤ) (hH2 : a ^ 2 ∣ a) :
    a ∈ ({(-1 : ℤ), (0 : ℤ), (1 : ℤ)} : Set ℤ) := by
  -- 1. obtain k: def:divides d := a², n := a, from H2
  obtain ⟨k, s1⟩ := ((Parley.Items.Stdlib.Divisibility.def_divides (d := a ^ 2) (n := a))).mp (by parley_set_side)
  -- 2. axi:excluded-middle P := a = 0
  have s2 : a = 0 ∨ a ≠ 0 := by first | exact (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := a = 0)) | exact ((Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := a = 0))).symm | simpa using (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := a = 0)) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := a = 0)) | (have h := (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := a = 0)); parley_set_side)
  -- 3. cases, from 2
  have s3 : a ∈ ({(-1 : ℤ), (0 : ℤ), (1 : ℤ)} : Set ℤ) := by
    rcases s2 with hC1 | hC2
    · skip
      -- 3.1. inspection
      have s3_1 : (0 : ℤ) ∈ ({(-1 : ℤ), (0 : ℤ), (1 : ℤ)} : Set ℤ) := by parley_set_side
      -- 3.2. substitute a = 0 (C1) into line 3.1
      have s3_2 : a ∈ ({(-1 : ℤ), (0 : ℤ), (1 : ℤ)} : Set ℤ) := by parley_subst_at hC1 s3_1
      all_goals parley_set_side
    · skip
      -- 3.3. algebra, from 1
      have s3_3 : a * k * a = 1 * a := by linear_combination (norm := parley_norm) (-1) * s1
      -- 3.4. mun:multiply-cancel a := a·k, b := 1, c := a, from C2, 3.3
      have s3_4 : a * k = 1 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := a * k) (b := (1 : ℤ)) (c := a) (by parley_set_side) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := a * k) (b := (1 : ℤ)) (c := a) (by parley_set_side) (by parley_set_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := a * k) (b := (1 : ℤ)) (c := a) (by parley_set_side) (by parley_set_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := a * k) (b := (1 : ℤ)) (c := a) (by parley_set_side) (by parley_set_side)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := a * k) (b := (1 : ℤ)) (c := a) (by parley_set_side) (by parley_set_side))).symm | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := a * k) (b := (1 : ℤ)) (c := a) (by parley_set_side) (by parley_set_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := a * k) (b := (1 : ℤ)) (c := a) (by parley_set_side) (by parley_set_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := a * k) (b := (1 : ℤ)) (c := a) (by parley_set_side) (by parley_set_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := a * k) (b := (1 : ℤ)) (c := a) (by parley_set_side) (by parley_set_side)); parley_set_side)
      -- 3.5. mun:nonneg-or-neg x := a
      have s3_5 : a ≥ 0 ∨ a < 0 := by first | exact (Parley.Items.Stdlib.Numbers.mun_nonneg_or_neg (x := a)) | exact ((Parley.Items.Stdlib.Numbers.mun_nonneg_or_neg (x := a))).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_nonneg_or_neg (x := a)) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_nonneg_or_neg (x := a)) | (have h := (Parley.Items.Stdlib.Numbers.mun_nonneg_or_neg (x := a)); parley_set_side)
      -- 3.6. cases, from 3.5
      have s3_6 : a ∈ ({(-1 : ℤ), (0 : ℤ), (1 : ℤ)} : Set ℤ) := by
        rcases s3_5 with hC3 | hC4
        · skip
          -- 3.6.1. inequalities, from C2, C3
          have s3_6_1 : a > 0 := by parley_order
          -- 3.6.2. mun:pos-int-nat m := a, from 3.6.1
          have s3_6_2 : 0 < a := by first | exact (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := a) (by parley_set_side)) | exact ((Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := a) (by parley_set_side))).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := a) (by parley_set_side)) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := a) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := a) (by parley_set_side)); parley_set_side)
          lift a to ℕ using s3_6_2.le
          -- 3.6.3. restate 3.4
          have s3_6_3 : 1 = (a : ℤ) * k := by parley_set_side
          -- 3.6.4. def:divides d := a, n := 1, from 3.6.3
          have s3_6_4 : (a : ℤ) ∣ (1 : ℤ) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_divides (d := (a : ℤ)) (n := (1 : ℤ)))).mpr ⟨k, by parley_set_side⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (a : ℤ)) (n := (1 : ℤ)))).mpr ⟨k, by parley_set_side⟩; parley_set_side)
          -- 3.6.5. inspection
          have s3_6_5 : (1 : ℤ) ∈ ({(-1 : ℤ), (0 : ℤ), (1 : ℤ)} : Set ℤ) := by parley_set_side
          -- 3.6.6. substitute
          have s3_6_6 : (a : ℤ) ∈ ({(-1 : ℤ), (0 : ℤ), (1 : ℤ)} : Set ℤ) := by
            have c1 : 1 = (a : ℤ) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := a) (by parley_set_side) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := a) (by parley_set_side) (by parley_set_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := a) (by parley_set_side) (by parley_set_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := a) (by parley_set_side) (by parley_set_side)) | exact_mod_cast ((Parley.Items.Stdlib.Divisibility.mun_divides_one (d := a) (by parley_set_side) (by parley_set_side))).symm | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := a) (by parley_set_side) (by parley_set_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := a) (by parley_set_side) (by parley_set_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := a) (by parley_set_side) (by parley_set_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := a) (by parley_set_side) (by parley_set_side)); parley_set_side)
            have row1 : (a : ℤ) ∈ ({(-1 : ℤ), (0 : ℤ), (1 : ℤ)} : Set ℤ) := by parley_subst_at c1 s3_6_5
            exact row1
          all_goals parley_set_side
        · skip
          -- 3.6.7. inequalities
          have s3_6_7 : -a > 0 := by parley_order
          -- 3.6.8. mun:pos-int-nat m := −a, from 3.6.7
          have s3_6_8 : 0 < -a := by first | exact (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := -a) (by parley_set_side)) | exact ((Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := -a) (by parley_set_side))).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := -a) (by parley_set_side)) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := -a) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := -a) (by parley_set_side)); parley_set_side)
          -- 3.6.9. algebra, from 3.4
          have s3_6_9 : 1 = -a * -k := by linear_combination (norm := parley_norm) (-1) * s3_4
          -- 3.6.10. def:divides d := −a, n := 1, from 3.6.9
          have s3_6_10 : -a ∣ (1 : ℤ) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_divides (d := -a) (n := (1 : ℤ)))).mpr ⟨-k, by parley_set_side⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_divides (d := -a) (n := (1 : ℤ)))).mpr ⟨-k, by parley_set_side⟩; parley_set_side)
          -- 3.6.11. mun:divides-one d := −a, from 3.6.8, 3.6.10
          have s3_6_11 : -a = 1 := by first | (have h := (Int.toNat_of_nonneg (show (0 : ℤ) ≤ (-a) by parley_set_side) ▸ (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := (-a).toNat) (by (try rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ (-a) by parley_set_side)]); parley_set_side) (by (try rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ (-a) by parley_set_side)]); parley_set_side))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Int.toNat_of_nonneg (show (0 : ℤ) ≤ (-a) by parley_set_side) ▸ (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := (-a).toNat) (by (try rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ (-a) by parley_set_side)]); parley_set_side) (by (try rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ (-a) by parley_set_side)]); parley_set_side))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | (have h := (Int.toNat_of_nonneg (show (0 : ℤ) ≤ (-a) by parley_set_side) ▸ (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := (-a).toNat) (by (try rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ (-a) by parley_set_side)]); parley_set_side) (by (try rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ (-a) by parley_set_side)]); parley_set_side))); exact_mod_cast h) | (have h := (Int.toNat_of_nonneg (show (0 : ℤ) ≤ (-a) by parley_set_side) ▸ (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := (-a).toNat) (by (try rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ (-a) by parley_set_side)]); parley_set_side) (by (try rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ (-a) by parley_set_side)]); parley_set_side))); exact_mod_cast h.symm) | (have h := (Int.toNat_of_nonneg (show (0 : ℤ) ≤ (-a) by parley_set_side) ▸ (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := (-a).toNat) (by (try rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ (-a) by parley_set_side)]); parley_set_side) (by (try rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ (-a) by parley_set_side)]); parley_set_side))); simp (disch := parley_set_side) only [parley_cast_toNat] at h; (try push_cast at h ⊢); linear_combination (norm := parley_norm) h) | (have h := (Int.toNat_of_nonneg (show (0 : ℤ) ≤ (-a) by parley_set_side) ▸ (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := (-a).toNat) (by (try rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ (-a) by parley_set_side)]); parley_set_side) (by (try rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ (-a) by parley_set_side)]); parley_set_side))); rify; linear_combination (norm := parley_norm) h) | (have h := (Int.toNat_of_nonneg (show (0 : ℤ) ≤ (-a) by parley_set_side) ▸ (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := (-a).toNat) (by (try rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ (-a) by parley_set_side)]); parley_set_side) (by (try rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ (-a) by parley_set_side)]); parley_set_side))); qify; linear_combination (norm := parley_norm) h) | (have h := (Int.toNat_of_nonneg (show (0 : ℤ) ≤ (-a) by parley_set_side) ▸ (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := (-a).toNat) (by (try rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ (-a) by parley_set_side)]); parley_set_side) (by (try rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ (-a) by parley_set_side)]); parley_set_side))); parley_int_power h) | (have h := (Int.toNat_of_nonneg (show (0 : ℤ) ≤ (-a) by parley_set_side) ▸ (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := (-a).toNat) (by (try rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ (-a) by parley_set_side)]); parley_set_side) (by (try rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ (-a) by parley_set_side)]); parley_set_side))); parley_set_side)
          -- 3.6.12. inspection
          have s3_6_12 : (-1 : ℤ) ∈ ({(-1 : ℤ), (0 : ℤ), (1 : ℤ)} : Set ℤ) := by parley_set_side
          -- 3.6.13. substitute
          have s3_6_13 : a ∈ ({(-1 : ℤ), (0 : ℤ), (1 : ℤ)} : Set ℤ) := by
            have c1 : -1 = a := by linear_combination (norm := parley_norm) s3_6_11
            have row1 : a ∈ ({(-1 : ℤ), (0 : ℤ), (1 : ℤ)} : Set ℤ) := by parley_subst_at c1 s3_6_12
            exact row1
          all_goals parley_set_side
      all_goals parley_set_side
  all_goals exact s3

end Parley.Proofs.Hammack.SquareDividesItself.SquareDividesItself
