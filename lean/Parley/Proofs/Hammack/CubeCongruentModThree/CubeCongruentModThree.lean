module

public import LeanBridges
public import Parley.Items.Stdlib.Divisibility
public import Parley.Proofs.Hammack.CubeCongruentModThree.ResidueModThree

/-! Written from proofs/hammack/cube-congruent-mod-three.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.CubeCongruentModThree.CubeCongruentModThree

theorem cube_congruent_mod_three (a : ℤ) :
    (a ^ 3) ≡ a [ZMOD (3 : ℤ)] := by
  -- 1. mun:mod-natural b := 3
  have s1 : 0 ≤ a % (3 : ℤ) := by first | exact (Parley.Items.Stdlib.Divisibility.mun_mod_natural (a := a) (b := 3) (by parley_side)) | exact ((Parley.Items.Stdlib.Divisibility.mun_mod_natural (a := a) (b := 3) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_mod_natural (a := a) (b := 3) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_mod_natural (a := a) (b := 3) (by parley_side)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_natural (a := a) (b := 3) (by parley_side)); parley_side)
  -- 2. mun:mod-less b := 3
  have s2 : a % (3 : ℤ) < 3 := by first | linarith [(Parley.Items.Stdlib.Divisibility.mun_mod_less (a := a) (b := 3) (by parley_side))] | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_less (a := a) (b := 3) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_mod_less (a := a) (b := 3) (by parley_side)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_less (a := a) (b := 3) (by parley_side)); parley_side)
  -- 3. thm:residue-mod-three r := a mod 3, from 1, 2
  have s3 : (a % (3 : ℤ) = 0 ∨ a % (3 : ℤ) = 1) ∨ a % (3 : ℤ) = 2 := by first | exact (Int.toNat_of_nonneg (show (0 : ℤ) ≤ (a % (3 : ℤ)) by parley_side) ▸ (Parley.Proofs.Hammack.CubeCongruentModThree.ResidueModThree.residue_mod_three (r := (a % (3 : ℤ)).toNat) (by parley_side))) | exact ((Int.toNat_of_nonneg (show (0 : ℤ) ≤ (a % (3 : ℤ)) by parley_side) ▸ (Parley.Proofs.Hammack.CubeCongruentModThree.ResidueModThree.residue_mod_three (r := (a % (3 : ℤ)).toNat) (by parley_side)))).symm | simpa using (Int.toNat_of_nonneg (show (0 : ℤ) ≤ (a % (3 : ℤ)) by parley_side) ▸ (Parley.Proofs.Hammack.CubeCongruentModThree.ResidueModThree.residue_mod_three (r := (a % (3 : ℤ)).toNat) (by parley_side))) | exact_mod_cast (Int.toNat_of_nonneg (show (0 : ℤ) ≤ (a % (3 : ℤ)) by parley_side) ▸ (Parley.Proofs.Hammack.CubeCongruentModThree.ResidueModThree.residue_mod_three (r := (a % (3 : ℤ)).toNat) (by parley_side))) | (have h := (Int.toNat_of_nonneg (show (0 : ℤ) ≤ (a % (3 : ℤ)) by parley_side) ▸ (Parley.Proofs.Hammack.CubeCongruentModThree.ResidueModThree.residue_mod_three (r := (a % (3 : ℤ)).toNat) (by parley_side))); parley_side)
  -- 4. obtain q: mun:mod-remainder m := 3, r := a mod 3, from 1, 2
  obtain ⟨q, s4⟩ := ((Int.toNat_of_nonneg (show (0 : ℤ) ≤ (a % (3 : ℤ)) by parley_side) ▸ (Parley.Items.Stdlib.Divisibility.mun_mod_remainder (a := a) (m := 3) (by parley_side) (r := (a % (3 : ℤ)).toNat) (by parley_side)))).mp (by parley_side)
  -- 5. cases, from 3
  have s5 : (3 : ℤ) ∣ a ^ 3 - a := by
    rcases s3 with (hC1 | hC2) | hC3
    · skip
      -- 5.1. substitute a mod 3 = 0 (C1) into line 4
      have s5_1 : q * 3 = a := by parley_subst_at hC1 s4
      -- 5.2. calculation
      have s5_2 : a ^ 3 - a = 3 * (9 * q ^ 3 - q) := by
        calc a ^ 3 - a = (q * 3) ^ 3 - q * 3 := by parley_subst s5_1
          _ = 3 * (9 * q ^ 3 - q) := by parley_ring
      -- 5.3. def:divides d := 3, n := a³ − a, from 5.2
      have s5_3 : (3 : ℤ) ∣ a ^ 3 - a := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_divides (d := (3 : ℤ)) (n := a ^ 3 - a))).mpr ⟨9 * q ^ 3 - q, by parley_side⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (3 : ℤ)) (n := a ^ 3 - a))).mpr ⟨9 * q ^ 3 - q, by parley_side⟩; parley_side)
      all_goals parley_side
    · skip
      -- 5.4. substitute a mod 3 = 1 (C2) into line 4
      have s5_4 : q * 3 + 1 = a := by parley_subst_at hC2 s4
      -- 5.5. calculation
      have s5_5 : a ^ 3 - a = 3 * (9 * q ^ 3 + 9 * q ^ 2 + 2 * q) := by
        calc a ^ 3 - a = (q * 3 + 1) ^ 3 - (q * 3 + 1) := by parley_subst s5_4
          _ = 3 * (9 * q ^ 3 + 9 * q ^ 2 + 2 * q) := by parley_ring
      -- 5.6. def:divides d := 3, n := a³ − a, from 5.5
      have s5_6 : (3 : ℤ) ∣ a ^ 3 - a := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_divides (d := (3 : ℤ)) (n := a ^ 3 - a))).mpr ⟨9 * q ^ 3 + 9 * q ^ 2 + 2 * q, by parley_side⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (3 : ℤ)) (n := a ^ 3 - a))).mpr ⟨9 * q ^ 3 + 9 * q ^ 2 + 2 * q, by parley_side⟩; parley_side)
      all_goals parley_side
    · skip
      -- 5.7. substitute a mod 3 = 2 (C3) into line 4
      have s5_7 : q * 3 + 2 = a := by parley_subst_at hC3 s4
      -- 5.8. calculation
      have s5_8 : a ^ 3 - a = 3 * (9 * q ^ 3 + 18 * q ^ 2 + 11 * q + 2) := by
        calc a ^ 3 - a = (q * 3 + 2) ^ 3 - (q * 3 + 2) := by parley_subst s5_7
          _ = 3 * (9 * q ^ 3 + 18 * q ^ 2 + 11 * q + 2) := by parley_ring
      -- 5.9. def:divides d := 3, n := a³ − a, from 5.8
      have s5_9 : (3 : ℤ) ∣ a ^ 3 - a := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_divides (d := (3 : ℤ)) (n := a ^ 3 - a))).mpr ⟨9 * q ^ 3 + 18 * q ^ 2 + 11 * q + 2, by parley_side⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (3 : ℤ)) (n := a ^ 3 - a))).mpr ⟨9 * q ^ 3 + 18 * q ^ 2 + 11 * q + 2, by parley_side⟩; parley_side)
      all_goals parley_side
  -- 6. def:congruent-mod, from 5
  have s6 : (a ^ 3) ≡ a [ZMOD (3 : ℤ)] := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := (3 : ℤ)) (a := a ^ 3) (b := a))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := (3 : ℤ)) (a := a ^ 3) (b := a))).mpr (by parley_side); parley_side)
  all_goals parley_side

end Parley.Proofs.Hammack.CubeCongruentModThree.CubeCongruentModThree
