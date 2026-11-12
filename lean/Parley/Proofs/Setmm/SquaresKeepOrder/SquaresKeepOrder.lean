module

public import Tactics
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/setmm/squares-keep-order.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.SquaresKeepOrder.SquaresKeepOrder

theorem squares_keep_order (a : ℝ) (b : ℝ) (hH3 : 0 ≤ a) (hH4 : a ≤ b) :
    a ^ 2 ≤ b ^ 2 := by
  -- 1. axi:trichotomy x := b − a
  have s1 : (b - a < 0 ∨ b - a = 0) ∨ 0 < b - a := by exact (Parley.Items.Stdlib.Numbers.axi_trichotomy (x := b - a))
  -- 2. cases, from 1
  rcases s1 with (hC1 | hC2) | hC3
  · skip
    -- 2.1. inequalities
    have s2_1 : b < a := by linarith only [hC1]
    -- 2.2. inequalities, from 2.1
    have s2_2 : ¬ a ≤ b := by linarith only [s2_1]
    exact absurd hH4 s2_2
  · skip
    -- 2.3. inequalities
    have s2_3 : a = b := by linarith only [hC2]
    -- 2.4. substitute a = b (line 2.3)
    have s2_4 : a ^ 2 = b ^ 2 := by (have h := congrArg (fun t : ℝ => t ^ 2) s2_3; push_cast at h ⊢; all_goals exact_mod_cast h)
    -- 2.5. inequalities
    linarith only [s2_4]
  · skip
    -- 2.6. inequalities
    have s2_6 : a < b := by linarith only [hC3]
    -- 2.7. transitivity, from H3, H4
    have s2_7 : b ≥ 0 := by exact le_trans hH3 hH4
    -- 2.8. mun:square-less x := a, y := b, from H3, 2.6, 2.7
    have s2_8 : a ^ 2 < b ^ 2 := by exact ((Parley.Items.Stdlib.Numbers.mun_square_less (x := a) (y := b) hH3 s2_7)).mp s2_6
    -- 2.9. inequalities
    linarith only [s2_8]

end Parley.Proofs.Setmm.SquaresKeepOrder.SquaresKeepOrder
