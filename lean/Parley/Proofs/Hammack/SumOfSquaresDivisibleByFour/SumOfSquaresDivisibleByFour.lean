module

public import ArithTactics
public import NormTactics
public import SubstTactics
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

/-! Written from proofs/hammack/sum-of-squares-divisible-by-four.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.SumOfSquaresDivisibleByFour.SumOfSquaresDivisibleByFour

set_option maxHeartbeats 400000 in
theorem sum_of_squares_divisible_by_four (a : ℤ) (b : ℤ) (hH3 : (4 : ℤ) ∣ a ^ 2 + b ^ 2) :
    ¬ (Odd a ∧ Odd b) := by
  -- 1. obtain k: def:divides, from H3
  obtain ⟨k, s1⟩ := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (4 : ℤ)) (n := a ^ 2 + b ^ 2))).mp hH3
  -- 2. contradiction
  intro hS
  -- 2.1. obtain m: def:odd n := a, from S
  obtain ⟨m, s2_1⟩ := ((Parley.Items.Stdlib.Divisibility.def_odd (n := a))).mp hS.1
  -- 2.2. obtain n: def:odd n := b, from S
  obtain ⟨n, s2_2⟩ := ((Parley.Items.Stdlib.Divisibility.def_odd (n := b))).mp hS.2
  -- 2.3. substitute a = 2m + 1 (line 2.1)
  have s2_3 : a ^ 2 = (2 * m + 1) ^ 2 := by parley_subst s2_1
  -- 2.4. substitute b = 2n + 1 (line 2.2)
  have s2_4 : b ^ 2 = (2 * n + 1) ^ 2 := by parley_subst s2_2
  -- 2.5. algebra, from 1, 2.3, 2.4
  have s2_5 : (2 * m + 1) ^ 2 + (2 * n + 1) ^ 2 = 4 * k := by linear_combination (norm := parley_norm) s1 + (-1) * s2_3 + (-1) * s2_4
  -- 2.6. algebra, from 2.5
  have s2_6 : 1 = 2 * (k - m ^ 2 - m - n ^ 2 - n) := by qify at *; linear_combination (norm := parley_norm) ((1 / 2 : ℚ)) * s2_5
  -- 2.7. def:even n := 1, from 2.6
  have s2_7 : Even (1 : ℤ) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_even (n := (1 : ℤ)))).mpr ⟨k - m ^ 2 - m - n ^ 2 - n, s2_6⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_even (n := (1 : ℤ)))).mpr ⟨k - m ^ 2 - m - n ^ 2 - n, s2_6⟩; parley_side)
  -- 2.8. mun:not-both n := 1, from 2.7
  have s2_8 : ¬ Odd (1 : ℤ) := by exact (Parley.Items.Stdlib.Divisibility.mun_not_both (n := (1 : ℤ)) s2_7)
  -- 2.9. arithmetic
  have s2_9 : Odd (1 : ℤ) := by parley_arith
  exact s2_8 s2_9

end Parley.Proofs.Hammack.SumOfSquaresDivisibleByFour.SumOfSquaresDivisibleByFour
