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

/-! Written from proofs/hammack/two-curves.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.TwoCurves.TwoCurves

set_option maxHeartbeats 400000 in
theorem two_curves (x : ℝ) (y : ℝ) :
    (x ^ 3 + x ^ 2 * y = y ^ 2 + x * y ↔ y = x ^ 2 ∨ y = -x) := by
  -- the theorem. both directions
  constructor
  · skip
    intro hD1
    -- 1. algebra, from D1
    have s1 : (y - x ^ 2) * (y + x) = 0 := by linear_combination (norm := parley_norm) (-1) * hD1
    -- 2. axi:excluded-middle P := y + x = 0
    have s2 : y + x = 0 ∨ y + x ≠ 0 := (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := y + x = 0))
    -- 3. cases, from 2
    rcases s2 with hC1 | hC2
    · skip
      -- 3.1. algebra, from C1
      have s3_1 : y = -x := by linear_combination (norm := parley_norm) hC1
      -- 3.2. mun:or-right, from 3.1
      exact (Parley.Items.Stdlib.Reasoning.mun_or_right (P := y = x ^ 2) (Q := y = -x) s3_1)
    · skip
      -- 3.3. algebra, from 1
      have s3_3 : (y - x ^ 2) * (y + x) = 0 * (y + x) := by linear_combination (norm := parley_norm) s1
      -- 3.4. mun:multiply-cancel a := y − x², b := 0, c := y + x, from C2, 3.3
      have s3_4 : y - x ^ 2 = 0 := (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := y - x ^ 2) (b := (0 : ℝ)) (c := y + x) (by parley_side) (by parley_side))
      -- 3.5. algebra, from 3.4
      have s3_5 : y = x ^ 2 := by linear_combination (norm := parley_norm) s3_4
      -- 3.6. mun:or-left, from 3.5
      exact (Parley.Items.Stdlib.Reasoning.mun_or_left (P := y = x ^ 2) (Q := y = -x) s3_5)
  · skip
    intro hD2
    -- 4. cases, from D2
    rcases hD2 with hC3 | hC4
    · skip
      -- 4.1. algebra, from C3
      linear_combination (norm := parley_norm) (-x - y) * hC3
    · skip
      -- 4.2. algebra, from C4
      linear_combination (norm := parley_norm) (x ^ 2 - y) * hC4

end Parley.Proofs.Hammack.TwoCurves.TwoCurves
