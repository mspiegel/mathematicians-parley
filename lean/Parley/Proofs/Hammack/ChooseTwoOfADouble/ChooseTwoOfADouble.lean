module

public import Parley.Library
public import Parley.Proofs.Hammack.BinomialOfTwo.BinomialOfTwo

/-! Written from proofs/hammack/choose-two-of-a-double.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.ChooseTwoOfADouble.ChooseTwoOfADouble

theorem choose_two_of_a_double (n : ℕ) :
    (Parley.Library.choose (2 * (n : ℤ)) (2 : ℤ) : ℤ) = 2 * (Parley.Library.choose (n : ℤ) (2 : ℤ) : ℤ) + (n : ℤ) ^ 2 := by
  -- 1. thm:binomial-of-two m := 2n
  have s1 : 2 * (Parley.Library.choose (2 * (n : ℤ)) (2 : ℤ) : ℤ) = 2 * (n : ℤ) * (2 * (n : ℤ) - 1) := by first | linear_combination (norm := parley_norm) (Parley.Proofs.Hammack.BinomialOfTwo.BinomialOfTwo.binomial_of_two (m := 2 * n)) | (have h := (Parley.Proofs.Hammack.BinomialOfTwo.BinomialOfTwo.binomial_of_two (m := 2 * n)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | exact_mod_cast (Parley.Proofs.Hammack.BinomialOfTwo.BinomialOfTwo.binomial_of_two (m := 2 * n)) | exact_mod_cast ((Parley.Proofs.Hammack.BinomialOfTwo.BinomialOfTwo.binomial_of_two (m := 2 * n))).symm | (have h := (Parley.Proofs.Hammack.BinomialOfTwo.BinomialOfTwo.binomial_of_two (m := 2 * n)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Hammack.BinomialOfTwo.BinomialOfTwo.binomial_of_two (m := 2 * n)); qify; linear_combination (norm := parley_norm) h)
  -- 2. thm:binomial-of-two m := n
  have s2 : 2 * (Parley.Library.choose (n : ℤ) (2 : ℤ) : ℤ) = (n : ℤ) * ((n : ℤ) - 1) := by first | linear_combination (norm := parley_norm) (Parley.Proofs.Hammack.BinomialOfTwo.BinomialOfTwo.binomial_of_two (m := n)) | (have h := (Parley.Proofs.Hammack.BinomialOfTwo.BinomialOfTwo.binomial_of_two (m := n)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | exact_mod_cast (Parley.Proofs.Hammack.BinomialOfTwo.BinomialOfTwo.binomial_of_two (m := n)) | exact_mod_cast ((Parley.Proofs.Hammack.BinomialOfTwo.BinomialOfTwo.binomial_of_two (m := n))).symm | (have h := (Parley.Proofs.Hammack.BinomialOfTwo.BinomialOfTwo.binomial_of_two (m := n)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Hammack.BinomialOfTwo.BinomialOfTwo.binomial_of_two (m := n)); qify; linear_combination (norm := parley_norm) h)
  -- 3. algebra, from 1, 2
  have s3 : (Parley.Library.choose (2 * (n : ℤ)) (2 : ℤ) : ℤ) = 2 * (Parley.Library.choose (n : ℤ) (2 : ℤ) : ℤ) + (n : ℤ) ^ 2 := by qify at *; linear_combination (norm := parley_norm) ((1 / 2 : ℚ)) * s1 + (-1) * s2
  all_goals parley_side

end Parley.Proofs.Hammack.ChooseTwoOfADouble.ChooseTwoOfADouble
