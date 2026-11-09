module

public import OrderTactics
public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/hammack/square-minus-three.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.SquareMinusThree.FourTimesBetween

theorem four_times_between (j : ℤ) (r : ℤ) (hH3 : r > 0) (hH4 : r < 4) :
    4 * j ≠ r := by
  -- 1. mun:nonneg-or-neg x := j − 1
  have s1 : j - 1 ≥ 0 ∨ j - 1 < 0 := by exact (Parley.Items.Stdlib.Numbers.mun_nonneg_or_neg (x := j - 1))
  -- 2. cases, from 1
  rcases s1 with hC1 | hC2
  · skip
    -- 2.1. inequalities
    have s2_1 : 4 * j ≥ 4 := by parley_order
    -- 2.2. transitivity, from H4, 2.1
    have s2_2 : r < 4 * j := by parley_order
    -- 2.3. inequalities
    parley_side
  · skip
    -- 2.4. inequalities, from C2
    have s2_4 : j < 1 := by parley_order
    -- 2.5. mun:integer-step m := j, n := 1, from 2.4
    have s2_5 : j + 1 ≤ 1 := by exact (Parley.Items.Stdlib.Numbers.mun_integer_step (m := j) (n := (1 : ℤ)) s2_4)
    -- 2.6. inequalities
    have s2_6 : 4 * j ≤ 0 := by parley_order
    -- 2.7. transitivity, from 2.6, H3
    have s2_7 : 4 * j < r := by parley_order
    -- 2.8. inequalities
    parley_side

end Parley.Proofs.Hammack.SquareMinusThree.FourTimesBetween
