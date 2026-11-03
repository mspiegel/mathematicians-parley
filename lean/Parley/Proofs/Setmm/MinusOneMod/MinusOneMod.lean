module

public import Tactics
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/setmm/minus-one-mod.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.MinusOneMod.MinusOneMod

theorem minus_one_mod (M : ℕ) (hH1 : 0 < M) :
    (-1 : ℤ) % (M : ℤ) = (M : ℤ) - 1 := by
  -- 1. algebra
  have s1 : -1 * (M : ℤ) + ((M : ℤ) - 1) = -1 := by parley_ring
  -- 2. exhibit, from 1
  have s2 : ∃ q : ℤ, q * (M : ℤ) + ((M : ℤ) - 1) = -1 := ⟨(-1 : ℤ), by parley_side⟩
  -- 3. mun:nat-minus-one n := M
  have s3 : 0 ≤ (M : ℤ) - 1 := by first | exact (Parley.Items.Stdlib.Numbers.mun_nat_minus_one (n := M) (by parley_side)) | exact ((Parley.Items.Stdlib.Numbers.mun_nat_minus_one (n := M) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_nat_minus_one (n := M) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_nat_minus_one (n := M) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_nat_minus_one (n := M) (by parley_side)); parley_side)
  -- 4. mun:mod-remainder a := −1, m := M, r := M − 1, from 2, 3
  have r19_1 : (M : ℤ) - 1 < (M : ℤ) := by parley_order
  have s4 : (-1 : ℤ) % (M : ℤ) = (M : ℤ) - 1 := by first | (assumption; done) | exact ((Int.toNat_of_nonneg (show (0 : ℤ) ≤ ((M : ℤ) - 1) by parley_side) ▸ (Parley.Items.Stdlib.Divisibility.mun_mod_remainder (a := (-1 : ℤ)) (m := M) (by parley_side) (r := ((M : ℤ) - 1).toNat) (by (try rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ ((M : ℤ) - 1) by parley_side)]); parley_side)))).mpr (by parley_side) | (have h := ((Int.toNat_of_nonneg (show (0 : ℤ) ≤ ((M : ℤ) - 1) by parley_side) ▸ (Parley.Items.Stdlib.Divisibility.mun_mod_remainder (a := (-1 : ℤ)) (m := M) (by parley_side) (r := ((M : ℤ) - 1).toNat) (by (try rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ ((M : ℤ) - 1) by parley_side)]); parley_side)))).mpr (by parley_side); parley_side)
  all_goals exact s4

end Parley.Proofs.Setmm.MinusOneMod.MinusOneMod
