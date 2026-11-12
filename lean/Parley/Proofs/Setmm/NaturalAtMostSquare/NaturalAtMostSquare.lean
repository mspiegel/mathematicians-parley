module

public import AlgebraTactics
public import OrderTactics
public import Tactics
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/setmm/natural-at-most-square.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.NaturalAtMostSquare.NaturalAtMostSquare

theorem natural_at_most_square (n : ℤ) (hH1 : 0 < n) :
    n ≤ n ^ 2 := by
  -- 1. inequalities, from H1
  have s1 : 1 ≤ n := by linarith only [hH1]
  -- 2. mun:multiply-le x := 1, y := n, c := n, from 1
  have r12_1 : n > 0 := by linarith only [s1]
  have s2 : n * 1 ≤ n * n := by exact (Parley.Items.Stdlib.Numbers.mun_multiply_le (x := (1 : ℤ)) (y := n) (c := n) s1 r12_1)
  -- 3. algebra
  have s3 : n ^ 2 = n * n := by parley_ring
  -- 4. transitivity, from 2, 3
  parley_order

end Parley.Proofs.Setmm.NaturalAtMostSquare.NaturalAtMostSquare
