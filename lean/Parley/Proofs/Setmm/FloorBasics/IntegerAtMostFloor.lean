module

public import ArithTactics
public import OrderTactics
public import Tactics
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/setmm/floor-basics.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.FloorBasics.IntegerAtMostFloor

theorem integer_at_most_floor (A : ℝ) (B : ℤ) :
    ((B : ℝ) ≤ A ↔ B ≤ ⌊A⌋) := by
  -- 1. mun:floor-integer x := A
  -- 2. mun:floor-below x := A
  have s2 : (⌊A⌋ : ℝ) ≤ A := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_floor_below (x := A))] | (have h := (Parley.Items.Stdlib.Numbers.mun_floor_below (x := A)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_floor_below (x := A)) | (have h := (Parley.Items.Stdlib.Numbers.mun_floor_below (x := A)); parley_side)
  -- 3. mun:floor-above x := A
  have s3 : A < (⌊A⌋ : ℝ) + 1 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_floor_above (x := A))] | (have h := (Parley.Items.Stdlib.Numbers.mun_floor_above (x := A)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_floor_above (x := A)) | (have h := (Parley.Items.Stdlib.Numbers.mun_floor_above (x := A)); parley_side)
  -- 4. both directions
  have s4 : (B : ℝ) ≤ A ↔ B ≤ ⌊A⌋ := by
    constructor
    · skip
      intro hC1
      by_contra hc_hS
      have hS : ¬ B ≤ ⌊A⌋ := by parley_suppose hc_hS
      -- 4.1. inequalities, from S
      have s4_1 : ⌊A⌋ < B := by parley_order
      -- 4.2. mun:integer-step m := ⌊A⌋, n := B, from 1, 4.1
      have s4_2 : ⌊A⌋ + 1 ≤ B := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_integer_step (m := ⌊A⌋) (n := B) s4_1)] | (have h := (Parley.Items.Stdlib.Numbers.mun_integer_step (m := ⌊A⌋) (n := B) s4_1); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_integer_step (m := ⌊A⌋) (n := B) s4_1) | (have h := (Parley.Items.Stdlib.Numbers.mun_integer_step (m := ⌊A⌋) (n := B) s4_1); parley_side)
      -- 4.3. transitivity, from 3, 4.2
      have s4_3 : A < (B : ℝ) := by parley_order
      -- 4.4. inequalities, from 4.3
      have s4_4 : ¬ (B : ℝ) ≤ A := by parley_side
      all_goals parley_side
    · skip
      intro hC2
      -- 4.5. transitivity, from C2, 2
      have s4_5 : (B : ℝ) ≤ A := by parley_order
      all_goals parley_side
  all_goals exact s4

end Parley.Proofs.Setmm.FloorBasics.IntegerAtMostFloor
