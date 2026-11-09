module

public import AlgebraTactics
public import ArithTactics
public import NormTactics
public import Tactics
public import Mathlib.Algebra.Group.Even
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Rat.Init
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Qify
public import Parley.Items.Stdlib.Divisibility
public import Parley.Proofs.Wiedijk.Sqrt2Irrational.EvenSquare

/-! Written from proofs/hammack/square-minus-four-b-minus-two.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.SquareMinusFourBMinusTwo.SquareMinusFourBMinusTwo

set_option maxHeartbeats 400000 in
theorem square_minus_four_b_minus_two (a : ℤ) (b : ℤ) :
    a ^ 2 - 4 * b - 2 ≠ 0 := by
  -- the theorem. contradiction
  intro hS
  -- 1. algebra, from S
  have s1 : a ^ 2 = 4 * b + 2 := by linear_combination (norm := parley_norm) hS
  -- 2. algebra, from 1
  have s2 : a ^ 2 = 2 * (2 * b + 1) := by linear_combination (norm := parley_norm) s1
  -- 3. def:even n := a², from 2
  have s3 : Even (a ^ 2) := ((Parley.Items.Stdlib.Divisibility.def_even (n := a ^ 2))).mpr ⟨2 * b + 1, s2⟩
  -- 4. thm:even-square n := a, from 3
  have s4 : Even a := by exact (Parley.Proofs.Wiedijk.Sqrt2Irrational.EvenSquare.even_square (n := a) (by parley_side))
  -- 5. obtain k: def:even n := a, from 4
  obtain ⟨k, s5⟩ := ((Parley.Items.Stdlib.Divisibility.def_even (n := a))).mp s4
  -- 6. calculation
  have s6 : 4 * k ^ 2 = 4 * b + 2 := by
    calc 4 * k ^ 2 = (2 * k) ^ 2 := by parley_ring
      _ = a ^ 2 := by (have h := congrArg (fun t : ℤ => t ^ 2) (s5).symm; push_cast at h ⊢; all_goals exact_mod_cast h)
      _ = 4 * b + 2 := by exact s1
  -- 7. algebra, from 6
  have s7 : 1 = 2 * (k ^ 2 - b) := by qify at *; linear_combination (norm := parley_norm) (-(1 / 2 : ℚ)) * s6
  -- 8. def:even n := 1, from 7
  have s8 : Even (1 : ℤ) := ((Parley.Items.Stdlib.Divisibility.def_even (n := (1 : ℤ)))).mpr ⟨k ^ 2 - b, s7⟩
  -- 9. mun:not-both n := 1, from 8
  have s9 : ¬ Odd (1 : ℤ) := by exact (Parley.Items.Stdlib.Divisibility.mun_not_both (n := (1 : ℤ)) s8)
  -- 10. arithmetic
  have s10 : Odd (1 : ℤ) := by parley_arith
  exact s9 s10

end Parley.Proofs.Hammack.SquareMinusFourBMinusTwo.SquareMinusFourBMinusTwo
