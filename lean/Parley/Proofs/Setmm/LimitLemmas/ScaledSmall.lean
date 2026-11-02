module

public import LeanBridges
public import Parley.Items.Stdlib.Numbers
public import Parley.Proofs.Setmm.LimitLemmas.AbsNonneg

/-! Written from proofs/setmm/limit-lemmas.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.LimitLemmas.ScaledSmall

theorem scaled_small (C : ℝ) (u : ℝ) (ε : ℝ) (hH4 : ε > 0) (hH5 : abs u < ε / (2 * (abs C + 1))) :
    abs (C * u) < ε := by
  -- 1. mun:abs-real x := C
  -- 2. thm:abs-nonneg x := C
  have s2 : abs C ≥ 0 := by first | linarith [(Parley.Proofs.Setmm.LimitLemmas.AbsNonneg.abs_nonneg (x := C))] | (have h := (Parley.Proofs.Setmm.LimitLemmas.AbsNonneg.abs_nonneg (x := C)); push_cast at h; linarith) | exact_mod_cast (Parley.Proofs.Setmm.LimitLemmas.AbsNonneg.abs_nonneg (x := C)) | (have h := (Parley.Proofs.Setmm.LimitLemmas.AbsNonneg.abs_nonneg (x := C)); parley_side)
  set d : ℝ := abs C + 1 with hD1
  -- 3. inequalities, from D1, 2
  have s3 : d > 0 := by parley_side
  -- 4. inequalities
  have s4 : 2 * d ≠ 0 := by parley_side
  -- 5. inequalities, from D1, H5, 4
  have s5 : abs u < ε / (2 * d) := by parley_side
  -- 6. inequalities
  have r89_1 : d ≠ 0 := by parley_side
  have s6 : abs u ≤ ε / (2 * d) := by parley_side
  -- 7. mun:multiply-le x := |u|, y := ε/(2·d), c := d, from 3, 6
  have s7 : d * abs u ≤ d * (ε / (2 * d)) := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_multiply_le (x := abs u) (y := ε / (2 * d)) (c := d) (by parley_side) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_le (x := abs u) (y := ε / (2 * d)) (c := d) (by parley_side) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_multiply_le (x := abs u) (y := ε / (2 * d)) (c := d) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_le (x := abs u) (y := ε / (2 * d)) (c := d) (by parley_side) (by parley_side)); parley_side)
  -- 8. algebra
  have r98_1 : 2 * d ≠ 0 := by parley_side
  have s8 : d * (ε / (2 * d)) = ε / 2 := by parley_ring
  -- 9. algebra, from D1
  have s9 : d * abs u = abs C * abs u + abs u := by
    try simp only [hD1] at *
    try push_cast at *
    parley_ring
  -- 10. thm:abs-nonneg x := u
  have s10 : abs u ≥ 0 := by first | linarith [(Parley.Proofs.Setmm.LimitLemmas.AbsNonneg.abs_nonneg (x := u))] | (have h := (Parley.Proofs.Setmm.LimitLemmas.AbsNonneg.abs_nonneg (x := u)); push_cast at h; linarith) | exact_mod_cast (Parley.Proofs.Setmm.LimitLemmas.AbsNonneg.abs_nonneg (x := u)) | (have h := (Parley.Proofs.Setmm.LimitLemmas.AbsNonneg.abs_nonneg (x := u)); parley_side)
  -- 11. inequalities
  have s11 : abs C * abs u ≤ abs C * abs u + abs u := by parley_side
  -- 12. transitivity, from 11, 9, 7, 8
  have r114_1 : d ≠ 0 := by parley_side
  have s12 : abs C * abs u ≤ ε / 2 := by parley_side
  -- 13. mun:abs-product x := C, y := u
  have s13 : abs (C * u) = abs C * abs u := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_abs_product (x := C) (y := u)) | (have h := (Parley.Items.Stdlib.Numbers.mun_abs_product (x := C) (y := u)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_abs_product (x := C) (y := u)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_abs_product (x := C) (y := u)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_abs_product (x := C) (y := u))).symm | (have h := (Parley.Items.Stdlib.Numbers.mun_abs_product (x := C) (y := u)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_abs_product (x := C) (y := u)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_abs_product (x := C) (y := u)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.mun_abs_product (x := C) (y := u)); parley_side)
  -- 14. inequalities
  have s14 : ε / 2 < ε := by parley_side
  -- 15. transitivity, from 13, 12, 14
  have s15 : abs (C * u) < ε := by parley_side
  all_goals parley_side

end Parley.Proofs.Setmm.LimitLemmas.ScaledSmall
