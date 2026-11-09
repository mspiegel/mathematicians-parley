module

public import OrderTactics
public import Tactics
public import Batteries.Tactic.Init
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers
public import Parley.Proofs.Setmm.MultiplyingBounds.MultiplyingBounds

/-! Written from proofs/setmm/multiplying-bounds.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.MultiplyingBounds.SquareOrder

set_option maxHeartbeats 400000 in
theorem square_order (A : ℝ) (B : ℝ) (hH3 : A ≥ 0) (hH4 : B ≥ 0) :
    (A < B ↔ A * A < B * B) := by
  -- the theorem. both directions
  constructor
  · skip
    intro hD1
    -- 1. thm:multiplying-bounds C := A, D := B, from D1, H3
    exact (Parley.Proofs.Setmm.MultiplyingBounds.MultiplyingBounds.multiplying_bounds (A := A) (B := B) (C := A) (D := B) hH3 hD1 hH3 hD1)
  · skip
    intro hD2
    by_contra hS
    -- 2. inequalities, from S
    have s2 : B ≤ A := by parley_order
    -- 3. inequalities
    have s3 : A - B ≥ 0 := by parley_order
    -- 4. mun:product-nonneg x := A − B, y := B, from H4, 3
    have s4 : (A - B) * B ≥ 0 := by exact (Parley.Items.Stdlib.Numbers.mun_product_nonneg (x := A - B) (y := B) (by parley_side) (by parley_side))
    -- 5. mun:product-nonneg x := A − B, y := A, from H3, 3
    have s5 : (A - B) * A ≥ 0 := by exact (Parley.Items.Stdlib.Numbers.mun_product_nonneg (x := A - B) (y := A) (by parley_side) (by parley_side))
    -- 6. inequalities
    have s6 : A * B - B * B ≥ 0 := by parley_order
    -- 7. inequalities
    have s7 : A * A - A * B ≥ 0 := by parley_order
    -- 8. inequalities, from 6, 7
    have s8 : A * A - B * B ≥ 0 := by parley_order
    -- 9. inequalities
    have s9 : B * B ≤ A * A := by parley_order
    -- 10. inequalities, from 9
    have s10 : ¬ A * A < B * B := by parley_side
    exact s10 hD2

end Parley.Proofs.Setmm.MultiplyingBounds.SquareOrder
