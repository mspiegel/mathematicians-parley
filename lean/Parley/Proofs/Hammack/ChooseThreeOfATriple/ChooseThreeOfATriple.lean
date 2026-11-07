module

public import Counting
public import FactorialTactics
public import NormTactics
public import PowerTactics
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
public import Mathlib.Tactic.Rify
public import Parley.Proofs.Hammack.BinomialOfThree.BinomialOfThree
public import Parley.Proofs.Hammack.BinomialOfTwo.BinomialOfTwo

/-! Written from proofs/hammack/choose-three-of-a-triple.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.ChooseThreeOfATriple.ChooseThreeOfATriple

theorem choose_three_of_a_triple (n : ℤ) (hH1 : 0 ≤ n) :
    (LeanBridges.Counting.choose (3 * n) (3 : ℤ) : ℤ) = 3 * (LeanBridges.Counting.choose n (3 : ℤ) : ℤ) + 6 * n * (LeanBridges.Counting.choose n (2 : ℤ) : ℤ) + n ^ 3 := by
  -- 1. thm:binomial-of-three m := 3n
  have s1 : 6 * (LeanBridges.Counting.choose (3 * n) (3 : ℤ) : ℤ) = 3 * n * (3 * n - 1) * (3 * n - 2) := by first | linear_combination (norm := parley_norm) (Parley.Proofs.Hammack.BinomialOfThree.BinomialOfThree.binomial_of_three (m := 3 * n) (by parley_side)) | (have h := (Parley.Proofs.Hammack.BinomialOfThree.BinomialOfThree.binomial_of_three (m := 3 * n) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Hammack.BinomialOfThree.BinomialOfThree.binomial_of_three (m := 3 * n) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Proofs.Hammack.BinomialOfThree.BinomialOfThree.binomial_of_three (m := 3 * n) (by parley_side)) | exact_mod_cast ((Parley.Proofs.Hammack.BinomialOfThree.BinomialOfThree.binomial_of_three (m := 3 * n) (by parley_side))).symm | (have h := (Parley.Proofs.Hammack.BinomialOfThree.BinomialOfThree.binomial_of_three (m := 3 * n) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Hammack.BinomialOfThree.BinomialOfThree.binomial_of_three (m := 3 * n) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Hammack.BinomialOfThree.BinomialOfThree.binomial_of_three (m := 3 * n) (by parley_side)); parley_int_power h) | (have h := (Parley.Proofs.Hammack.BinomialOfThree.BinomialOfThree.binomial_of_three (m := 3 * n) (by parley_side)); parley_side)
  -- 2. thm:binomial-of-three m := n
  have s2 : 6 * (LeanBridges.Counting.choose n (3 : ℤ) : ℤ) = n * (n - 1) * (n - 2) := by first | linear_combination (norm := parley_norm) (Parley.Proofs.Hammack.BinomialOfThree.BinomialOfThree.binomial_of_three (m := n) (by parley_side)) | (have h := (Parley.Proofs.Hammack.BinomialOfThree.BinomialOfThree.binomial_of_three (m := n) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Hammack.BinomialOfThree.BinomialOfThree.binomial_of_three (m := n) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Proofs.Hammack.BinomialOfThree.BinomialOfThree.binomial_of_three (m := n) (by parley_side)) | exact_mod_cast ((Parley.Proofs.Hammack.BinomialOfThree.BinomialOfThree.binomial_of_three (m := n) (by parley_side))).symm | (have h := (Parley.Proofs.Hammack.BinomialOfThree.BinomialOfThree.binomial_of_three (m := n) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Hammack.BinomialOfThree.BinomialOfThree.binomial_of_three (m := n) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Hammack.BinomialOfThree.BinomialOfThree.binomial_of_three (m := n) (by parley_side)); parley_int_power h) | (have h := (Parley.Proofs.Hammack.BinomialOfThree.BinomialOfThree.binomial_of_three (m := n) (by parley_side)); parley_side)
  -- 3. thm:binomial-of-two m := n
  have s3 : 2 * (LeanBridges.Counting.choose n (2 : ℤ) : ℤ) = n * (n - 1) := by first | linear_combination (norm := parley_norm) (Parley.Proofs.Hammack.BinomialOfTwo.BinomialOfTwo.binomial_of_two (m := n) (by parley_side)) | (have h := (Parley.Proofs.Hammack.BinomialOfTwo.BinomialOfTwo.binomial_of_two (m := n) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Hammack.BinomialOfTwo.BinomialOfTwo.binomial_of_two (m := n) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Proofs.Hammack.BinomialOfTwo.BinomialOfTwo.binomial_of_two (m := n) (by parley_side)) | exact_mod_cast ((Parley.Proofs.Hammack.BinomialOfTwo.BinomialOfTwo.binomial_of_two (m := n) (by parley_side))).symm | (have h := (Parley.Proofs.Hammack.BinomialOfTwo.BinomialOfTwo.binomial_of_two (m := n) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Hammack.BinomialOfTwo.BinomialOfTwo.binomial_of_two (m := n) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Hammack.BinomialOfTwo.BinomialOfTwo.binomial_of_two (m := n) (by parley_side)); parley_int_power h) | (have h := (Parley.Proofs.Hammack.BinomialOfTwo.BinomialOfTwo.binomial_of_two (m := n) (by parley_side)); parley_side)
  -- 4. algebra, from 1, 2, 3
  have s4 : (LeanBridges.Counting.choose (3 * n) (3 : ℤ) : ℤ) = 3 * (LeanBridges.Counting.choose n (3 : ℤ) : ℤ) + 6 * n * (LeanBridges.Counting.choose n (2 : ℤ) : ℤ) + n ^ 3 := by qify at *; linear_combination (norm := parley_norm) ((1 / 6 : ℚ)) * s1 + (-(1 / 2 : ℚ)) * s2 + (-3 * (n : ℚ)) * s3
  all_goals exact s4

end Parley.Proofs.Hammack.ChooseThreeOfATriple.ChooseThreeOfATriple
