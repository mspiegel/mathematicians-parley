module

public import Parley.Items.Stdlib.Numbers
public import Parley.Library
public import Parley.Proofs.Wiedijk.DivisibilityByThree.CongruentTimes

/-! Written from proofs/wiedijk/divisibility-by-three.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.DivisibilityByThree.TenPowerCongruent

theorem ten_power_congruent (k : ℕ) :
    (10 ^ k : ℤ) ≡ (1 : ℤ) [ZMOD (3 : ℤ)] := by
  -- 1. induction on m starting at 0
  have s1 : ∀ m : ℕ, (10 ^ m : ℤ) ≡ (1 : ℤ) [ZMOD (3 : ℤ)] := by
    intro m
    induction m with
    | zero =>
      -- 1.1. calculation
      have s1_1 : (10 ^ 0 : ℤ) ≡ (1 : ℤ) [ZMOD (3 : ℤ)] := by
        calc (10 ^ 0 : ℤ) = 1 := by norm_num
          _ ≡ 1 [ZMOD (3 : ℤ)] := by norm_num
      all_goals parley_side
    | succ m hIH =>
      -- 1.2. mun:exponent-step a := 10
      have s1_2 : (10 ^ (m + 1) : ℤ) = 10 ^ m * 10 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (10 : ℤ)) (m := m)) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (10 : ℤ)) (m := m)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (10 : ℤ)) (m := m)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (10 : ℤ)) (m := m))).symm
      -- 1.3. calculation
      have s1_3 : (10 ^ (m + 1) : ℤ) ≡ (1 : ℤ) [ZMOD (3 : ℤ)] := by
        calc (10 ^ (m + 1) : ℤ) = 10 ^ m * 10 := by parley_side
          _ ≡ 1 * 10 [ZMOD (3 : ℤ)] := by first | exact (Parley.Proofs.Wiedijk.DivisibilityByThree.CongruentTimes.congruent_times (a := (10 ^ m : ℤ)) (b := (1 : ℤ)) (c := (10 : ℤ)) (n := 3) (by parley_side) (by parley_side)) | exact ((Parley.Proofs.Wiedijk.DivisibilityByThree.CongruentTimes.congruent_times (a := (10 ^ m : ℤ)) (b := (1 : ℤ)) (c := (10 : ℤ)) (n := 3) (by parley_side) (by parley_side))).symm | simpa using (Parley.Proofs.Wiedijk.DivisibilityByThree.CongruentTimes.congruent_times (a := (10 ^ m : ℤ)) (b := (1 : ℤ)) (c := (10 : ℤ)) (n := 3) (by parley_side) (by parley_side)) | exact_mod_cast (Parley.Proofs.Wiedijk.DivisibilityByThree.CongruentTimes.congruent_times (a := (10 ^ m : ℤ)) (b := (1 : ℤ)) (c := (10 : ℤ)) (n := 3) (by parley_side) (by parley_side))
          _ ≡ 10 [ZMOD (3 : ℤ)] := by norm_num
          _ ≡ 1 [ZMOD (3 : ℤ)] := by norm_num
      all_goals parley_side
  -- 2. instantiate m := k in line 1
  have s2 : (10 ^ k : ℤ) ≡ (1 : ℤ) [ZMOD (3 : ℤ)] := by first | exact (s1 k) | exact ((s1 k)).symm | simpa using (s1 k) | exact_mod_cast (s1 k)
  all_goals parley_side

end Parley.Proofs.Wiedijk.DivisibilityByThree.TenPowerCongruent
