module

public import OrderTactics
public import Tactics
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith.Frontend
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/setmm/floor-basics.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.FloorBasics.FloorAtMostOneMore

theorem floor_at_most_one_more (A : ℝ) :
    A ≤ (⌊A⌋ : ℝ) + 1 := by
  -- 1. mun:floor-integer x := A
  -- 2. mun:floor-above x := A
  have s2 : A < (⌊A⌋ : ℝ) + 1 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_floor_above (x := A))] | (have h := (Parley.Items.Stdlib.Numbers.mun_floor_above (x := A)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_floor_above (x := A)) | (have h := (Parley.Items.Stdlib.Numbers.mun_floor_above (x := A)); parley_side)
  -- 3. inequalities
  have s3 : A ≤ (⌊A⌋ : ℝ) + 1 := by parley_order
  all_goals exact s3

end Parley.Proofs.Setmm.FloorBasics.FloorAtMostOneMore
