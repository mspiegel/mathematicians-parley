module

public import Tactics
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/setmm/root-order.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.RootOrder.RootOrder

theorem root_order (A : ℝ) (B : ℝ) (hH3 : 0 ≤ A) (hH4 : 0 ≤ B) :
    (A < B ↔ Real.sqrt A < Real.sqrt B) := by
  -- 1. def:sqrt x := A, from H3
  have s1a : Real.sqrt A ≥ 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := A) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := A) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := A) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := A) (by parley_side)); parley_side)
  have s1b : Real.sqrt A ^ 2 = A := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := A) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := A) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := A) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := A) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := A) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := A) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := A) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := A) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := A) (by parley_side)); parley_side)
  -- 2. def:sqrt x := B, from H4
  have s2a : Real.sqrt B ≥ 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := B) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := B) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := B) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := B) (by parley_side)); parley_side)
  have s2b : Real.sqrt B ^ 2 = B := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := B) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := B) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := B) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := B) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := B) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := B) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := B) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := B) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := B) (by parley_side)); parley_side)
  -- 3. both directions
  have s3 : A < B ↔ Real.sqrt A < Real.sqrt B := by
    constructor
    · skip
      intro hD1
      -- 3.1. transitivity, from 1, D1, 2
      have s3_1 : Real.sqrt A ^ 2 < Real.sqrt B ^ 2 := by parley_order
      -- 3.2. mun:square-less x := √A, y := √B, from 3.1
      have r28_3 : Real.sqrt A ≥ 0 := by parley_side
      have r28_4 : Real.sqrt B ≥ 0 := by parley_side
      have s3_2 : Real.sqrt A < Real.sqrt B := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Numbers.mun_square_less (x := Real.sqrt A) (y := Real.sqrt B) (by parley_side) (by parley_side))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_square_less (x := Real.sqrt A) (y := Real.sqrt B) (by parley_side) (by parley_side))).mpr (by parley_side); parley_side)
      all_goals parley_side
    · skip
      intro hD2
      -- 3.3. mun:square-less x := √A, y := √B, from D2
      have r38_3 : Real.sqrt A ≥ 0 := by parley_side
      have r38_4 : Real.sqrt B ≥ 0 := by parley_side
      have s3_3 : Real.sqrt A ^ 2 < Real.sqrt B ^ 2 := by first | linarith [((Parley.Items.Stdlib.Numbers.mun_square_less (x := Real.sqrt A) (y := Real.sqrt B) (by parley_side) (by parley_side))).mp (by parley_side)] | (have h := ((Parley.Items.Stdlib.Numbers.mun_square_less (x := Real.sqrt A) (y := Real.sqrt B) (by parley_side) (by parley_side))).mp (by parley_side); push_cast at h; linarith) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_square_less (x := Real.sqrt A) (y := Real.sqrt B) (by parley_side) (by parley_side))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_square_less (x := Real.sqrt A) (y := Real.sqrt B) (by parley_side) (by parley_side))).mp (by parley_side); parley_side)
      -- 3.4. transitivity, from 1, 3.3, 2
      have s3_4 : A < B := by parley_order
      all_goals parley_side
  all_goals parley_side

end Parley.Proofs.Setmm.RootOrder.RootOrder
