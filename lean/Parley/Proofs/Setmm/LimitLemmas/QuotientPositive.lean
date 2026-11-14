module

public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.Field
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/setmm/limit-lemmas.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.LimitLemmas.QuotientPositive

theorem quotient_positive (x : ℝ) (y : ℝ) (hH3 : x > 0) (hH4 : y > 0) :
    x / y > 0 := by
  -- 1. mun:quotient-nonneg, from H4
  have r35_1 : x ≥ 0 := by linarith only [hH3]
  have s1 : x / y ≥ 0 := by exact (Parley.Items.Stdlib.Numbers.mun_quotient_nonneg (x := x) (y := y) r35_1 hH4)
  -- 2. contradiction
  have s2 : x / y ≠ 0 := by
    intro hS
    -- 2.1. algebra, from S
    have r43_1 : y ≠ 0 := ne_of_gt (by linarith only [hH4])
    have s2_1 : x = 0 := by have hz1 : y ≠ 0 := r43_1; linear_combination (norm := (field)) (y) * hS
    -- 2.2. inequalities
    have s2_2 : x ≠ 0 := ne_of_gt (by linarith only [hH3])
    exact s2_2 s2_1
  -- 3. inequalities, from 1, 2
  have r52_1 : y ≠ 0 := ne_of_gt (by linarith only [hH4])
  exact Or.elim (Ne.lt_or_gt s2) (fun h1 => by linarith only [s1, h1]) (fun h1 => by linarith only [s1, h1])

end Parley.Proofs.Setmm.LimitLemmas.QuotientPositive
