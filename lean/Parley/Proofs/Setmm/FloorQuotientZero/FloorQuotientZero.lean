module

public import Tactics
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/setmm/floor-quotient-zero.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.FloorQuotientZero.FloorQuotientZero

theorem floor_quotient_zero (A : ℕ) (B : ℕ) (hH2 : 0 < B) :
    ((A : ℤ) < (B : ℤ) ↔ ⌊(A : ℚ) / (B : ℚ)⌋ = 0) := by
  -- 1. algebra
  have s1 : (B : ℚ) * ((A : ℚ) / (B : ℚ)) = (A : ℚ) := by parley_ring
  -- 2. mun:quotient-nonneg x := A, y := B, from H1, H2
  have s2 : 0 ≤ (A : ℚ) / (B : ℚ) := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_quotient_nonneg (x := (A : ℚ)) (y := (B : ℚ)) (by parley_side) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_quotient_nonneg (x := (A : ℚ)) (y := (B : ℚ)) (by parley_side) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_quotient_nonneg (x := (A : ℚ)) (y := (B : ℚ)) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_quotient_nonneg (x := (A : ℚ)) (y := (B : ℚ)) (by parley_side) (by parley_side)); parley_side)
  -- 3. both directions
  have s3 : (A : ℤ) < (B : ℤ) ↔ ⌊(A : ℚ) / (B : ℚ)⌋ = 0 := by
    constructor
    · skip
      intro hC1
      -- 3.1. transitivity, from 1, C1
      have s3_1 : (B : ℚ) * ((A : ℚ) / (B : ℚ)) < (B : ℚ) := by parley_side
      -- 3.2. mun:less-scaled x := A/B, y := 1, c := B, from H2, 3.1
      have s3_2 : (A : ℚ) / (B : ℚ) < 1 := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Numbers.mun_less_scaled (x := (A : ℚ) / (B : ℚ)) (y := (1 : ℚ)) (c := (B : ℚ)) (by parley_side))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_less_scaled (x := (A : ℚ) / (B : ℚ)) (y := (1 : ℚ)) (c := (B : ℚ)) (by parley_side))).mpr (by parley_side); parley_side)
      -- 3.3. mun:floor-between x := A/B, k := 0, from 2, 3.2
      have s3_3 : ⌊(A : ℚ) / (B : ℚ)⌋ = 0 := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Numbers.mun_floor_between (x := (A : ℚ) / (B : ℚ)) (k := (0 : ℤ)))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_floor_between (x := (A : ℚ) / (B : ℚ)) (k := (0 : ℤ)))).mpr (by parley_side); parley_side)
      all_goals parley_side
    · skip
      intro hC2
      -- 3.4. mun:floor-between x := A/B, k := 0, from C2
      have s3_4 : 0 ≤ (A : ℚ) / (B : ℚ) ∧ (A : ℚ) / (B : ℚ) < 1 := by first | exact ((Parley.Items.Stdlib.Numbers.mun_floor_between (x := (A : ℚ) / (B : ℚ)) (k := (0 : ℤ)))).mp (by parley_side) | exact (((Parley.Items.Stdlib.Numbers.mun_floor_between (x := (A : ℚ) / (B : ℚ)) (k := (0 : ℤ)))).mp (by parley_side)).symm | simpa using ((Parley.Items.Stdlib.Numbers.mun_floor_between (x := (A : ℚ) / (B : ℚ)) (k := (0 : ℤ)))).mp (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_floor_between (x := (A : ℚ) / (B : ℚ)) (k := (0 : ℤ)))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_floor_between (x := (A : ℚ) / (B : ℚ)) (k := (0 : ℤ)))).mp (by parley_side); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := ((Parley.Items.Stdlib.Numbers.mun_floor_between (x := (A : ℚ) / (B : ℚ)) (k := (0 : ℤ)))).mp (by parley_side); parley_side)
      -- 3.5. mun:less-scaled x := A/B, y := 1, c := B, from H2, 3.4
      have s3_5 : (B : ℚ) * ((A : ℚ) / (B : ℚ)) < (B : ℚ) := by first | linarith [((Parley.Items.Stdlib.Numbers.mun_less_scaled (x := (A : ℚ) / (B : ℚ)) (y := (1 : ℚ)) (c := (B : ℚ)) (by parley_side))).mp (by parley_side)] | (have h := ((Parley.Items.Stdlib.Numbers.mun_less_scaled (x := (A : ℚ) / (B : ℚ)) (y := (1 : ℚ)) (c := (B : ℚ)) (by parley_side))).mp (by parley_side); push_cast at h; linarith) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_less_scaled (x := (A : ℚ) / (B : ℚ)) (y := (1 : ℚ)) (c := (B : ℚ)) (by parley_side))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_less_scaled (x := (A : ℚ) / (B : ℚ)) (y := (1 : ℚ)) (c := (B : ℚ)) (by parley_side))).mp (by parley_side); parley_side)
      -- 3.6. transitivity, from 1, 3.5
      have s3_6 : (A : ℤ) < (B : ℤ) := by parley_side
      all_goals parley_side
  all_goals parley_side

end Parley.Proofs.Setmm.FloorQuotientZero.FloorQuotientZero
