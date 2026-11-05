module

public import Counting
public import FactorialTactics
public import PowerTactics
public import Tactics
public import Parley.Proofs.Hammack.BinomialOfThree.BinomialOfThree
public import Parley.Proofs.Hammack.BinomialOfTwo.BinomialOfTwo

/-! Written from proofs/hammack/choose-three-of-a-triple.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.ChooseThreeOfATriple.ChooseThreeOfATriple

theorem choose_three_of_a_triple (n : ℕ) :
    (LeanBridges.Counting.choose (3 * (n : ℤ)) (3 : ℤ) : ℤ) = 3 * (LeanBridges.Counting.choose (n : ℤ) (3 : ℤ) : ℤ) + 6 * (n : ℤ) * (LeanBridges.Counting.choose (n : ℤ) (2 : ℤ) : ℤ) + (n : ℤ) ^ 3 := by
  -- 1. thm:binomial-of-three m := 3n
  have s1 : 6 * (LeanBridges.Counting.choose (3 * (n : ℤ)) (3 : ℤ) : ℤ) = 3 * (n : ℤ) * (3 * (n : ℤ) - 1) * (3 * (n : ℤ) - 2) := by first | linear_combination (norm := parley_norm) (Parley.Proofs.Hammack.BinomialOfThree.BinomialOfThree.binomial_of_three (m := 3 * n)) | (have h := (Parley.Proofs.Hammack.BinomialOfThree.BinomialOfThree.binomial_of_three (m := 3 * n)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Hammack.BinomialOfThree.BinomialOfThree.binomial_of_three (m := 3 * n)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Proofs.Hammack.BinomialOfThree.BinomialOfThree.binomial_of_three (m := 3 * n)) | exact_mod_cast ((Parley.Proofs.Hammack.BinomialOfThree.BinomialOfThree.binomial_of_three (m := 3 * n))).symm | (have h := (Parley.Proofs.Hammack.BinomialOfThree.BinomialOfThree.binomial_of_three (m := 3 * n)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Hammack.BinomialOfThree.BinomialOfThree.binomial_of_three (m := 3 * n)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Hammack.BinomialOfThree.BinomialOfThree.binomial_of_three (m := 3 * n)); parley_int_power h) | (have h := (Parley.Proofs.Hammack.BinomialOfThree.BinomialOfThree.binomial_of_three (m := 3 * n)); parley_side)
  -- 2. thm:binomial-of-three m := n
  have s2 : 6 * (LeanBridges.Counting.choose (n : ℤ) (3 : ℤ) : ℤ) = (n : ℤ) * ((n : ℤ) - 1) * ((n : ℤ) - 2) := by first | linear_combination (norm := parley_norm) (Parley.Proofs.Hammack.BinomialOfThree.BinomialOfThree.binomial_of_three (m := n)) | (have h := (Parley.Proofs.Hammack.BinomialOfThree.BinomialOfThree.binomial_of_three (m := n)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Hammack.BinomialOfThree.BinomialOfThree.binomial_of_three (m := n)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Proofs.Hammack.BinomialOfThree.BinomialOfThree.binomial_of_three (m := n)) | exact_mod_cast ((Parley.Proofs.Hammack.BinomialOfThree.BinomialOfThree.binomial_of_three (m := n))).symm | (have h := (Parley.Proofs.Hammack.BinomialOfThree.BinomialOfThree.binomial_of_three (m := n)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Hammack.BinomialOfThree.BinomialOfThree.binomial_of_three (m := n)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Hammack.BinomialOfThree.BinomialOfThree.binomial_of_three (m := n)); parley_int_power h) | (have h := (Parley.Proofs.Hammack.BinomialOfThree.BinomialOfThree.binomial_of_three (m := n)); parley_side)
  -- 3. thm:binomial-of-two m := n
  have s3 : 2 * (LeanBridges.Counting.choose (n : ℤ) (2 : ℤ) : ℤ) = (n : ℤ) * ((n : ℤ) - 1) := by first | linear_combination (norm := parley_norm) (Parley.Proofs.Hammack.BinomialOfTwo.BinomialOfTwo.binomial_of_two (m := n)) | (have h := (Parley.Proofs.Hammack.BinomialOfTwo.BinomialOfTwo.binomial_of_two (m := n)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Hammack.BinomialOfTwo.BinomialOfTwo.binomial_of_two (m := n)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Proofs.Hammack.BinomialOfTwo.BinomialOfTwo.binomial_of_two (m := n)) | exact_mod_cast ((Parley.Proofs.Hammack.BinomialOfTwo.BinomialOfTwo.binomial_of_two (m := n))).symm | (have h := (Parley.Proofs.Hammack.BinomialOfTwo.BinomialOfTwo.binomial_of_two (m := n)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Hammack.BinomialOfTwo.BinomialOfTwo.binomial_of_two (m := n)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Hammack.BinomialOfTwo.BinomialOfTwo.binomial_of_two (m := n)); parley_int_power h) | (have h := (Parley.Proofs.Hammack.BinomialOfTwo.BinomialOfTwo.binomial_of_two (m := n)); parley_side)
  -- 4. algebra, from 1, 2, 3
  have s4 : (LeanBridges.Counting.choose (3 * (n : ℤ)) (3 : ℤ) : ℤ) = 3 * (LeanBridges.Counting.choose (n : ℤ) (3 : ℤ) : ℤ) + 6 * (n : ℤ) * (LeanBridges.Counting.choose (n : ℤ) (2 : ℤ) : ℤ) + (n : ℤ) ^ 3 := by qify at *; linear_combination (norm := parley_norm) ((1 / 6 : ℚ)) * s1 + (-(1 / 2 : ℚ)) * s2 + (-3 * (n : ℚ)) * s3
  all_goals exact s4

end Parley.Proofs.Hammack.ChooseThreeOfATriple.ChooseThreeOfATriple
