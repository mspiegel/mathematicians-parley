module

public import ArithTactics
public import OrderTactics
public import Tactics
public import Batteries.Tactic.Init
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.Ring.RingNF
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/setmm/floor-below-non-integer.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.FloorBelowNonInteger.FloorBelowNonInteger

theorem floor_below_non_integer (A : ℝ) (hH2 : ¬ (∃ m : ℤ, (m : ℝ) = A)) :
    (⌊A⌋ : ℝ) < A := by
  -- 1. mun:floor-below x := A
  have s1 : (⌊A⌋ : ℝ) ≤ A := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_floor_below (x := A))] | (have h := (Parley.Items.Stdlib.Numbers.mun_floor_below (x := A)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_floor_below (x := A)) | (have h := (Parley.Items.Stdlib.Numbers.mun_floor_below (x := A)); parley_side)
  -- 2. mun:floor-integer x := A
  -- 3. contradiction
  have s3 : (⌊A⌋ : ℝ) ≠ A := by
    by_contra hc_hS
    have hS : (⌊A⌋ : ℝ) = A := by parley_suppose hc_hS
    -- 3.1. substitute ⌊A⌋ = A (S) into line 2
    have s3_1 : ∃ m : ℤ, (m : ℝ) = A := ⟨⌊A⌋, by first | (push_cast; linarith [hS]) | (rw [hS]; push_cast; ring) | (rw [← hS]; push_cast; ring) | exact hS | exact hS.symm⟩
    all_goals parley_side
  -- 4. inequalities, from 1, 3
  have s4 : (⌊A⌋ : ℝ) < A := by parley_order
  all_goals exact s4

end Parley.Proofs.Setmm.FloorBelowNonInteger.FloorBelowNonInteger
