module

public import LeanBridges
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Reasoning
public import Parley.Proofs.Hammack.CubeCongruentModThree.ResidueModThree

/-! Written from proofs/hammack/rational-squares-sum-not-three.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.RationalSquaresSumNotThree.SquareModThree

theorem square_mod_three (n : ℤ) :
    ((3 : ℤ) ∣ n ^ 2 ∨ (3 : ℤ) ∣ n ^ 2 - 1) := by
  -- 1. mun:mod-natural a := n, b := 3
  have s1 : 0 ≤ n % (3 : ℤ) := by first | exact (Parley.Items.Stdlib.Divisibility.mun_mod_natural (a := n) (b := 3) (by parley_side)) | exact ((Parley.Items.Stdlib.Divisibility.mun_mod_natural (a := n) (b := 3) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_mod_natural (a := n) (b := 3) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_mod_natural (a := n) (b := 3) (by parley_side)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_natural (a := n) (b := 3) (by parley_side)); parley_side)
  -- 2. mun:mod-less a := n, b := 3
  have s2 : n % (3 : ℤ) < 3 := by first | linarith [(Parley.Items.Stdlib.Divisibility.mun_mod_less (a := n) (b := 3) (by parley_side))] | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_less (a := n) (b := 3) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_mod_less (a := n) (b := 3) (by parley_side)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_less (a := n) (b := 3) (by parley_side)); parley_side)
  -- 3. thm:residue-mod-three r := n mod 3, from 1, 2
  have s3 : (n % (3 : ℤ) = 0 ∨ n % (3 : ℤ) = 1) ∨ n % (3 : ℤ) = 2 := by first | exact (Int.toNat_of_nonneg (show (0 : ℤ) ≤ (n % (3 : ℤ)) by parley_side) ▸ (Parley.Proofs.Hammack.CubeCongruentModThree.ResidueModThree.residue_mod_three (r := (n % (3 : ℤ)).toNat) (by (try rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ (n % (3 : ℤ)) by parley_side)]); parley_side))) | exact ((Int.toNat_of_nonneg (show (0 : ℤ) ≤ (n % (3 : ℤ)) by parley_side) ▸ (Parley.Proofs.Hammack.CubeCongruentModThree.ResidueModThree.residue_mod_three (r := (n % (3 : ℤ)).toNat) (by (try rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ (n % (3 : ℤ)) by parley_side)]); parley_side)))).symm | simpa using (Int.toNat_of_nonneg (show (0 : ℤ) ≤ (n % (3 : ℤ)) by parley_side) ▸ (Parley.Proofs.Hammack.CubeCongruentModThree.ResidueModThree.residue_mod_three (r := (n % (3 : ℤ)).toNat) (by (try rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ (n % (3 : ℤ)) by parley_side)]); parley_side))) | exact_mod_cast (Int.toNat_of_nonneg (show (0 : ℤ) ≤ (n % (3 : ℤ)) by parley_side) ▸ (Parley.Proofs.Hammack.CubeCongruentModThree.ResidueModThree.residue_mod_three (r := (n % (3 : ℤ)).toNat) (by (try rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ (n % (3 : ℤ)) by parley_side)]); parley_side))) | (have h := (Int.toNat_of_nonneg (show (0 : ℤ) ≤ (n % (3 : ℤ)) by parley_side) ▸ (Parley.Proofs.Hammack.CubeCongruentModThree.ResidueModThree.residue_mod_three (r := (n % (3 : ℤ)).toNat) (by (try rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ (n % (3 : ℤ)) by parley_side)]); parley_side))); parley_side)
  -- 4. obtain q: mun:mod-remainder a := n, m := 3, r := n mod 3, from 1, 2
  obtain ⟨q, s4⟩ := ((Int.toNat_of_nonneg (show (0 : ℤ) ≤ (n % (3 : ℤ)) by parley_side) ▸ (Parley.Items.Stdlib.Divisibility.mun_mod_remainder (a := n) (m := 3) (by parley_side) (r := (n % (3 : ℤ)).toNat) (by (try rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ (n % (3 : ℤ)) by parley_side)]); parley_side)))).mp (by parley_side)
  -- 5. cases, from 3
  have s5 : (3 : ℤ) ∣ n ^ 2 ∨ (3 : ℤ) ∣ n ^ 2 - 1 := by
    rcases s3 with (hC1 | hC2) | hC3
    · skip
      -- 5.1. substitute n mod 3 = 0 (C1) into line 4
      have s5_1 : q * 3 = n := by parley_subst_at hC1 s4
      -- 5.2. algebra, from 5.1
      have s5_2 : n ^ 2 = 3 * (3 * q ^ 2) := by linear_combination (norm := parley_norm) (-n - 3 * q) * s5_1
      -- 5.3. def:divides d := 3, n := n², from 5.2
      have s5_3 : (3 : ℤ) ∣ n ^ 2 := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_divides (d := (3 : ℤ)) (n := n ^ 2))).mpr ⟨3 * q ^ 2, by parley_side⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (3 : ℤ)) (n := n ^ 2))).mpr ⟨3 * q ^ 2, by parley_side⟩; parley_side)
      -- 5.4. mun:or-left, from 5.3
      have s5_4 : (3 : ℤ) ∣ n ^ 2 ∨ (3 : ℤ) ∣ n ^ 2 - 1 := by first | exact (Parley.Items.Stdlib.Reasoning.mun_or_left (P := (3 : ℤ) ∣ n ^ 2) (Q := (3 : ℤ) ∣ n ^ 2 - 1) (by parley_side)) | exact ((Parley.Items.Stdlib.Reasoning.mun_or_left (P := (3 : ℤ) ∣ n ^ 2) (Q := (3 : ℤ) ∣ n ^ 2 - 1) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_or_left (P := (3 : ℤ) ∣ n ^ 2) (Q := (3 : ℤ) ∣ n ^ 2 - 1) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_or_left (P := (3 : ℤ) ∣ n ^ 2) (Q := (3 : ℤ) ∣ n ^ 2 - 1) (by parley_side)) | (have h := (Parley.Items.Stdlib.Reasoning.mun_or_left (P := (3 : ℤ) ∣ n ^ 2) (Q := (3 : ℤ) ∣ n ^ 2 - 1) (by parley_side)); parley_side)
      all_goals parley_side
    · skip
      -- 5.5. substitute n mod 3 = 1 (C2) into line 4
      have s5_5 : q * 3 + 1 = n := by parley_subst_at hC2 s4
      -- 5.6. algebra, from 5.5
      have s5_6 : n ^ 2 - 1 = 3 * (3 * q ^ 2 + 2 * q) := by linear_combination (norm := parley_norm) (-n - 3 * q - 1) * s5_5
      -- 5.7. def:divides d := 3, n := n² − 1, from 5.6
      have s5_7 : (3 : ℤ) ∣ n ^ 2 - 1 := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_divides (d := (3 : ℤ)) (n := n ^ 2 - 1))).mpr ⟨3 * q ^ 2 + 2 * q, by parley_side⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (3 : ℤ)) (n := n ^ 2 - 1))).mpr ⟨3 * q ^ 2 + 2 * q, by parley_side⟩; parley_side)
      -- 5.8. mun:or-right, from 5.7
      have s5_8 : (3 : ℤ) ∣ n ^ 2 ∨ (3 : ℤ) ∣ n ^ 2 - 1 := by first | exact (Parley.Items.Stdlib.Reasoning.mun_or_right (P := (3 : ℤ) ∣ n ^ 2) (Q := (3 : ℤ) ∣ n ^ 2 - 1) (by parley_side)) | exact ((Parley.Items.Stdlib.Reasoning.mun_or_right (P := (3 : ℤ) ∣ n ^ 2) (Q := (3 : ℤ) ∣ n ^ 2 - 1) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_or_right (P := (3 : ℤ) ∣ n ^ 2) (Q := (3 : ℤ) ∣ n ^ 2 - 1) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_or_right (P := (3 : ℤ) ∣ n ^ 2) (Q := (3 : ℤ) ∣ n ^ 2 - 1) (by parley_side)) | (have h := (Parley.Items.Stdlib.Reasoning.mun_or_right (P := (3 : ℤ) ∣ n ^ 2) (Q := (3 : ℤ) ∣ n ^ 2 - 1) (by parley_side)); parley_side)
      all_goals parley_side
    · skip
      -- 5.9. substitute n mod 3 = 2 (C3) into line 4
      have s5_9 : q * 3 + 2 = n := by parley_subst_at hC3 s4
      -- 5.10. algebra, from 5.9
      have s5_10 : n ^ 2 - 1 = 3 * (3 * q ^ 2 + 4 * q + 1) := by linear_combination (norm := parley_norm) (-n - 3 * q - 2) * s5_9
      -- 5.11. def:divides d := 3, n := n² − 1, from 5.10
      have s5_11 : (3 : ℤ) ∣ n ^ 2 - 1 := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_divides (d := (3 : ℤ)) (n := n ^ 2 - 1))).mpr ⟨3 * q ^ 2 + 4 * q + 1, by parley_side⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (3 : ℤ)) (n := n ^ 2 - 1))).mpr ⟨3 * q ^ 2 + 4 * q + 1, by parley_side⟩; parley_side)
      -- 5.12. mun:or-right, from 5.11
      have s5_12 : (3 : ℤ) ∣ n ^ 2 ∨ (3 : ℤ) ∣ n ^ 2 - 1 := by first | exact (Parley.Items.Stdlib.Reasoning.mun_or_right (P := (3 : ℤ) ∣ n ^ 2) (Q := (3 : ℤ) ∣ n ^ 2 - 1) (by parley_side)) | exact ((Parley.Items.Stdlib.Reasoning.mun_or_right (P := (3 : ℤ) ∣ n ^ 2) (Q := (3 : ℤ) ∣ n ^ 2 - 1) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_or_right (P := (3 : ℤ) ∣ n ^ 2) (Q := (3 : ℤ) ∣ n ^ 2 - 1) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_or_right (P := (3 : ℤ) ∣ n ^ 2) (Q := (3 : ℤ) ∣ n ^ 2 - 1) (by parley_side)) | (have h := (Parley.Items.Stdlib.Reasoning.mun_or_right (P := (3 : ℤ) ∣ n ^ 2) (Q := (3 : ℤ) ∣ n ^ 2 - 1) (by parley_side)); parley_side)
      all_goals parley_side
  all_goals parley_side

end Parley.Proofs.Hammack.RationalSquaresSumNotThree.SquareModThree
