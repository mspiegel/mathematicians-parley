module

public import NormTactics
public import Tactics
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Reasoning

/-! Written from proofs/hammack/equal-or-sum-five.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.EqualOrSumFive.EqualOrSumFive

theorem equal_or_sum_five (x : ℝ) (y : ℝ) (hH3 : x ^ 2 + 5 * y = y ^ 2 + 5 * x) :
    (x = y ∨ x + y = 5) := by
  -- 1. axi:excluded-middle P := x + y = 5
  have s1 : x + y = 5 ∨ x + y ≠ 5 := by exact (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := x + y = 5))
  -- 2. cases, from 1
  rcases s1 with hC1 | hC2
  · skip
    -- 2.1. mun:or-right P := x = y, Q := x + y = 5, from C1
    exact (Parley.Items.Stdlib.Reasoning.mun_or_right (P := x = y) (Q := x + y = 5) hC1)
  · skip
    -- 2.2. inequalities, from C2
    have s2_2 : x + y - 5 ≠ 0 := by parley_side
    -- 2.3. algebra, from H3
    have s2_3 : (x - y) * (x + y - 5) = 0 * (x + y - 5) := by linear_combination (norm := parley_norm) hH3
    -- 2.4. mun:multiply-cancel a := x − y, b := 0, c := x + y − 5, from 2.2, 2.3
    have s2_4 : x - y = 0 := by exact (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := x - y) (b := (0 : ℝ)) (c := x + y - 5) (by parley_side) (by parley_side))
    -- 2.5. algebra, from 2.4
    have s2_5 : x = y := by linear_combination (norm := parley_norm) s2_4
    -- 2.6. mun:or-left P := x = y, Q := x + y = 5, from 2.5
    exact (Parley.Items.Stdlib.Reasoning.mun_or_left (P := x = y) (Q := x + y = 5) s2_5)

end Parley.Proofs.Hammack.EqualOrSumFive.EqualOrSumFive
