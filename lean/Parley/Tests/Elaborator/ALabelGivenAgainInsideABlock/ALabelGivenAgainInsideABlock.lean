module

public import ArithTactics
public import OrderTactics
public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.Positivity.Basic

/-! Written from tests/elaborator/a-label-given-again-inside-a-block.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ALabelGivenAgainInsideABlock.ALabelGivenAgainInsideABlock

theorem a_label_given_again_inside_a_block :
    (∀ x : ℝ, x > 0 → x ≥ 0 ∧ x + 1 > 0) := by
  -- 1. proof
  intro x
  intro hJ
  -- 1.1. proof
  have s1_1 : ∀ y : ℝ, y > 0 → y + 1 > 0 := by
    intro y
    intro hJ
    -- 1.1.1. inequalities
    have s1_1_1 : y + 1 > 1 := by linarith only [hJ]
    -- 1.1.2. arithmetic
    have s1_1_2 : (1 : ℤ) > 0 := by parley_arith
    -- 1.1.3. transitivity, from 1.1.1, 1.1.2
    exact lt_trans (show (1 : ℝ) > 0 by exact_mod_cast s1_1_2) s1_1_1
  -- 1.2. instantiate y := x in line 1.1, from J
  have s1_2 : x + 1 > 0 := by exact (s1_1 x (by parley_side))
  -- 1.3. inequalities
  have s1_3 : x ≥ 0 := by parley_order
  -- 1.4. join 1.3, 1.2
  have s1_4 : x ≥ 0 ∧ x + 1 > 0 := by parley_side
  exact ⟨(s1_4).1, (s1_4).2⟩

end Parley.Tests.Elaborator.ALabelGivenAgainInsideABlock.ALabelGivenAgainInsideABlock
