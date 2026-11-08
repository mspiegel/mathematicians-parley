module

public import OrderTactics
public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Reasoning

/-! Written from proofs/setmm/average-at-most-an-end.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.AverageAtMostAnEnd.AverageAtMostAnEnd

theorem average_at_most_an_end (A : ℝ) (B : ℝ) :
    ((A + B) / 2 ≤ A ∨ (A + B) / 2 ≤ B) := by
  -- 1. mun:nonneg-or-neg x := B − A
  have s1 : B - A ≥ 0 ∨ B - A < 0 := (Parley.Items.Stdlib.Numbers.mun_nonneg_or_neg (x := B - A))
  -- 2. cases, from 1
  rcases s1 with hC1 | hC2
  · skip
    -- 2.1. inequalities
    have s2_1 : (A + B) / 2 ≤ B := by parley_order
    -- 2.2. mun:or-right, from 2.1
    exact (Parley.Items.Stdlib.Reasoning.mun_or_right (P := (A + B) / 2 ≤ A) (Q := (A + B) / 2 ≤ B) s2_1)
  · skip
    -- 2.3. inequalities
    have s2_3 : (A + B) / 2 ≤ A := by parley_order
    -- 2.4. mun:or-left, from 2.3
    exact (Parley.Items.Stdlib.Reasoning.mun_or_left (P := (A + B) / 2 ≤ A) (Q := (A + B) / 2 ≤ B) s2_3)

end Parley.Proofs.Setmm.AverageAtMostAnEnd.AverageAtMostAnEnd
