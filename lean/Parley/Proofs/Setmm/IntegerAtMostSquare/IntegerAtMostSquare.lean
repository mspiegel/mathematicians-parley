module

public import AlgebraTactics
public import NormTactics
public import Tactics
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/setmm/integer-at-most-square.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.IntegerAtMostSquare.IntegerAtMostSquare

theorem integer_at_most_square (n : ℤ) :
    n ≤ n ^ 2 := by
  -- 1. axi:trichotomy x := n
  have s1 : (n < 0 ∨ n = 0) ∨ 0 < n := by exact (Parley.Items.Stdlib.Numbers.axi_trichotomy (x := n))
  -- 2. mun:square-nonneg x := n
  have s2 : n ^ 2 ≥ 0 := by exact (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := n))
  -- 3. algebra
  have s3 : n ^ 2 = n * n := by parley_ring
  -- 4. cases, from 1
  rcases s1 with (hC1 | hC2) | hC3
  · skip
    -- 4.1. inequalities, from C1, 2
    have s4_1 : n < n ^ 2 := by linarith only [hC1, s2]
    -- 4.2. inequalities
    linarith only [s4_1]
  · skip
    -- 4.3. algebra, from C2
    have s4_3 : n * n = 0 := by linear_combination (norm := parley_norm) (n) * hC2
    -- 4.4. transitivity, from C2, 4.3, 3
    have s4_4 : n = n ^ 2 := by parley_side
    -- 4.5. inequalities
    linarith only [s4_4]
  · skip
    -- 4.6. mun:integer-step m := 0, from C3
    have s4_6 : 1 ≤ n := by simpa only [zero_add] using (Parley.Items.Stdlib.Numbers.mun_integer_step (m := (0 : ℤ)) (n := n) hC3)
    -- 4.7. mun:multiply-le x := 1, y := n, c := n, from C3, 4.6
    have s4_7 : n * 1 ≤ n * n := by exact (Parley.Items.Stdlib.Numbers.mun_multiply_le (x := (1 : ℤ)) (y := n) (c := n) s4_6 hC3)
    -- 4.8. inequalities
    linarith only [s4_7]

end Parley.Proofs.Setmm.IntegerAtMostSquare.IntegerAtMostSquare
