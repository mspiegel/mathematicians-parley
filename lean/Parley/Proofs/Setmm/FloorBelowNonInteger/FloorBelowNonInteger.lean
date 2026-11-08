module

public import OrderTactics
public import Tactics
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Rat.Floor
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Ring.RingNF
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/setmm/floor-below-non-integer.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.FloorBelowNonInteger.FloorBelowNonInteger

theorem floor_below_non_integer (A : ℝ) (hH2 : ¬ (∃ m : ℤ, (m : ℝ) = A)) :
    (⌊A⌋ : ℝ) < A := by
  -- 1. mun:floor-below x := A
  have s1 : (⌊A⌋ : ℝ) ≤ A := by exact (Parley.Items.Stdlib.Numbers.mun_floor_below (x := A))
  -- 2. mun:floor-integer x := A
  -- 3. contradiction
  have s3 : (⌊A⌋ : ℝ) ≠ A := by
    intro hS
    -- 3.1. substitute ⌊A⌋ = A (S) into line 2
    have s3_1 : ∃ m : ℤ, (m : ℝ) = A := ⟨⌊A⌋, by first | (push_cast; linarith [hS]) | (rw [hS]; push_cast; ring) | (rw [← hS]; push_cast; ring) | exact hS | exact hS.symm⟩
    exact hH2 s3_1
  -- 4. inequalities, from 1, 3
  parley_order

end Parley.Proofs.Setmm.FloorBelowNonInteger.FloorBelowNonInteger
