module

public import NormTactics
public import Tactics
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Rat.Init
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Divisibility
public import Parley.Proofs.Setmm.TriangularNumberInteger.TriangularNumberInteger

/-! Written from proofs/setmm/odd-square-less-one-over-eight.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.OddSquareLessOneOverEight.OddSquareLessOneOverEight

theorem odd_square_less_one_over_eight (n : ℤ) (hH2 : Odd n) :
    (∃ m : ℤ, (m : ℚ) = ((n : ℚ) ^ 2 - 1) / 8) := by
  -- 1. obtain k: def:odd, from H2
  obtain ⟨k, s1⟩ := ((Parley.Items.Stdlib.Divisibility.def_odd (n := n))).mp (by parley_side)
  -- 2. algebra, from 1
  have s2 : ((n : ℚ) ^ 2 - 1) / 8 = (k : ℚ) * ((k : ℚ) + 1) / 2 := by
    have s1_w : (n : ℚ) = 2 * (k : ℚ) + 1 := by have h := congrArg (fun x : ℤ => (x : ℚ)) s1; push_cast at h; linear_combination (norm := parley_norm) h
    linear_combination (norm := parley_norm) ((4 * (k : ℚ) + 2 * (n : ℚ) + 2) / ((8) * (2))) * s1_w
  -- 3. thm:triangular-number-integer n := k
  have s3 : ∃ m : ℤ, (m : ℚ) = (k : ℚ) * ((k : ℚ) + 1) / 2 := by exact (Parley.Proofs.Setmm.TriangularNumberInteger.TriangularNumberInteger.triangular_number_integer (n := k))
  -- 4. membership, from 2, 3
  have s4 : ∃ m : ℤ, (m : ℚ) = ((n : ℚ) ^ 2 - 1) / 8 := by parley_side
  all_goals exact s4

end Parley.Proofs.Setmm.OddSquareLessOneOverEight.OddSquareLessOneOverEight
