module

public import OrderTactics
public import SubstTactics
public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith.Frontend
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/setmm/squares-keep-order.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.SquaresKeepOrder.SquaresKeepOrder

set_option maxHeartbeats 400000 in
theorem squares_keep_order (a : ℝ) (b : ℝ) (hH3 : 0 ≤ a) (hH4 : a ≤ b) :
    a ^ 2 ≤ b ^ 2 := by
  -- 1. axi:trichotomy x := b − a
  have s1 : (b - a < 0 ∨ b - a = 0) ∨ 0 < b - a := by first | exact (Parley.Items.Stdlib.Numbers.axi_trichotomy (x := b - a)) | exact ((Parley.Items.Stdlib.Numbers.axi_trichotomy (x := b - a))).symm | simpa using (Parley.Items.Stdlib.Numbers.axi_trichotomy (x := b - a)) | exact_mod_cast (Parley.Items.Stdlib.Numbers.axi_trichotomy (x := b - a)) | (have h := (Parley.Items.Stdlib.Numbers.axi_trichotomy (x := b - a)); parley_side)
  -- 2. cases, from 1
  have s2 : a ^ 2 ≤ b ^ 2 := by
    rcases s1 with (hC1 | hC2) | hC3
    · skip
      -- 2.1. inequalities
      have s2_1 : b < a := by parley_order
      -- 2.2. inequalities, from 2.1
      have s2_2 : ¬ a ≤ b := by parley_side
      all_goals parley_side
    · skip
      -- 2.3. inequalities
      have s2_3 : a = b := by parley_side
      -- 2.4. substitute a = b (line 2.3)
      have s2_4 : a ^ 2 = b ^ 2 := by parley_subst s2_3
      -- 2.5. inequalities
      have s2_5 : a ^ 2 ≤ b ^ 2 := by parley_order
      all_goals parley_side
    · skip
      -- 2.6. inequalities
      have s2_6 : a < b := by parley_order
      -- 2.7. transitivity, from H3, H4
      have s2_7 : b ≥ 0 := by parley_order
      -- 2.8. mun:square-less x := a, y := b, from H3, 2.6, 2.7
      have s2_8 : a ^ 2 < b ^ 2 := by first | linarith [((Parley.Items.Stdlib.Numbers.mun_square_less (x := a) (y := b) (by parley_side) (by parley_side))).mp (by parley_side)] | (have h := ((Parley.Items.Stdlib.Numbers.mun_square_less (x := a) (y := b) (by parley_side) (by parley_side))).mp (by parley_side); push_cast at h; linarith) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_square_less (x := a) (y := b) (by parley_side) (by parley_side))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_square_less (x := a) (y := b) (by parley_side) (by parley_side))).mp (by parley_side); parley_side)
      -- 2.9. inequalities
      have s2_9 : a ^ 2 ≤ b ^ 2 := by parley_order
      all_goals parley_side
  all_goals exact s2

end Parley.Proofs.Setmm.SquaresKeepOrder.SquaresKeepOrder
