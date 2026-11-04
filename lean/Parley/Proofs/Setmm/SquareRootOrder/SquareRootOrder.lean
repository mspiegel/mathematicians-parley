module

public import ArithTactics
public import OrderTactics
public import PowerTactics
public import Tactics
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/setmm/square-root-order.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.SquareRootOrder.SquareRootOrder

theorem square_root_order (A : ℝ) (B : ℝ) (hH3 : 0 ≤ A) (hH4 : 0 ≤ B) :
    (A ≤ B ↔ Real.sqrt A ≤ Real.sqrt B) := by
  -- 1. def:sqrt x := A, from H3
  have s1a : Real.sqrt A ≥ 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := A) hH3)] | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := A) hH3); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := A) hH3) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := A) hH3); parley_side)
  have s1b : Real.sqrt A ^ 2 = A := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := A) hH3) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := A) hH3); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := A) hH3); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := A) hH3) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := A) hH3)).symm | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := A) hH3); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := A) hH3); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := A) hH3); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := A) hH3); parley_side)
  -- 2. def:sqrt x := B, from H4
  have s2a : Real.sqrt B ≥ 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := B) hH4)] | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := B) hH4); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := B) hH4) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := B) hH4); parley_side)
  have s2b : Real.sqrt B ^ 2 = B := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := B) hH4) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := B) hH4); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := B) hH4); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := B) hH4) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := B) hH4)).symm | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := B) hH4); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := B) hH4); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := B) hH4); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := B) hH4); parley_side)
  -- 3. both directions
  have s3 : A ≤ B ↔ Real.sqrt A ≤ Real.sqrt B := by
    constructor
    · skip
      intro hD1
      by_contra hc_hS1
      have hS1 : ¬ Real.sqrt A ≤ Real.sqrt B := by parley_suppose hc_hS1
      -- 3.1. inequalities, from S1
      have s3_1 : Real.sqrt B < Real.sqrt A := by parley_order
      -- 3.2. calculation
      have s3_2 : B < A := by
        calc B = Real.sqrt B ^ 2 := by parley_side
          _ < Real.sqrt A ^ 2 := by first | linarith [((Parley.Items.Stdlib.Numbers.mun_square_less (x := Real.sqrt B) (y := Real.sqrt A) (by parley_side) (by parley_side))).mp (by parley_side)] | (have h := ((Parley.Items.Stdlib.Numbers.mun_square_less (x := Real.sqrt B) (y := Real.sqrt A) (by parley_side) (by parley_side))).mp (by parley_side); push_cast at h; linarith) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_square_less (x := Real.sqrt B) (y := Real.sqrt A) (by parley_side) (by parley_side))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_square_less (x := Real.sqrt B) (y := Real.sqrt A) (by parley_side) (by parley_side))).mp (by parley_side); parley_side)
          _ = A := by parley_side
      -- 3.3. inequalities, from 3.2
      have s3_3 : ¬ A ≤ B := by parley_side
      all_goals parley_side
    · skip
      intro hD2
      by_contra hc_hS2
      have hS2 : ¬ A ≤ B := by parley_suppose hc_hS2
      -- 3.4. inequalities, from S2
      have s3_4 : B < A := by parley_order
      -- 3.5. calculation
      have s3_5 : Real.sqrt B ^ 2 < Real.sqrt A ^ 2 := by
        calc Real.sqrt B ^ 2 = B := by parley_side
          _ < A := by parley_side
          _ = Real.sqrt A ^ 2 := by parley_side
      -- 3.6. mun:square-less x := √B, y := √A, from 1, 2, 3.5
      have s3_6 : Real.sqrt B < Real.sqrt A := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Numbers.mun_square_less (x := Real.sqrt B) (y := Real.sqrt A) (by parley_side) (by parley_side))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_square_less (x := Real.sqrt B) (y := Real.sqrt A) (by parley_side) (by parley_side))).mpr (by parley_side); parley_side)
      -- 3.7. inequalities, from 3.6
      have s3_7 : ¬ Real.sqrt A ≤ Real.sqrt B := by parley_side
      all_goals parley_side
  all_goals exact s3

end Parley.Proofs.Setmm.SquareRootOrder.SquareRootOrder
