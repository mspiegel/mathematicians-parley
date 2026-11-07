module

public import Counting
public import FactorialTactics
public import NormTactics
public import Tactics
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Rat.Init
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Qify
public import Parley.Proofs.Hammack.BinomialOfTwo.BinomialOfTwo

/-! Written from proofs/hammack/choose-two-of-a-double.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.ChooseTwoOfADouble.ChooseTwoOfADouble

theorem choose_two_of_a_double (n : ℤ) (hH1 : 0 ≤ n) :
    (LeanBridges.Counting.choose (2 * n) (2 : ℤ) : ℤ) = 2 * (LeanBridges.Counting.choose n (2 : ℤ) : ℤ) + n ^ 2 := by
  -- 1. thm:binomial-of-two m := 2n
  have s1 : 2 * (LeanBridges.Counting.choose (2 * n) (2 : ℤ) : ℤ) = 2 * n * (2 * n - 1) := by exact (Parley.Proofs.Hammack.BinomialOfTwo.BinomialOfTwo.binomial_of_two (m := 2 * n) (by parley_side))
  -- 2. thm:binomial-of-two m := n
  have s2 : 2 * (LeanBridges.Counting.choose n (2 : ℤ) : ℤ) = n * (n - 1) := by exact (Parley.Proofs.Hammack.BinomialOfTwo.BinomialOfTwo.binomial_of_two (m := n) (by parley_side))
  -- 3. algebra, from 1, 2
  have s3 : (LeanBridges.Counting.choose (2 * n) (2 : ℤ) : ℤ) = 2 * (LeanBridges.Counting.choose n (2 : ℤ) : ℤ) + n ^ 2 := by qify at *; linear_combination (norm := parley_norm) ((1 / 2 : ℚ)) * s1 + (-1) * s2
  all_goals exact s3

end Parley.Proofs.Hammack.ChooseTwoOfADouble.ChooseTwoOfADouble
