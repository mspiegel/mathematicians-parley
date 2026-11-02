module

public import LeanBridges
public import Parley.Items.Stdlib.Counting
public import Parley.Proofs.Hammack.BinomialOfTwo.BinomialOfTwo

/-! Written from proofs/hammack/binomial-of-three.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.BinomialOfThree.BinomialOfThree

theorem binomial_of_three (m : ℕ) :
    6 * (LeanBridges.Counting.choose (m : ℤ) (3 : ℤ) : ℤ) = (m : ℤ) * ((m : ℤ) - 1) * ((m : ℤ) - 2) := by
  -- 1. induction on j starting at 0
  have s1 : ∀ j : ℕ, 6 * (LeanBridges.Counting.choose (j : ℤ) (3 : ℤ) : ℤ) = (j : ℤ) * ((j : ℤ) - 1) * ((j : ℤ) - 2) := by
    intro j
    induction j with
    | zero =>
      -- 1.1. arithmetic
      have s1_1 : (0 : ℤ) < 3 := by parley_arith
      -- 1.2. def:C n := 0, k := 3, from 1.1
      have s1_2 : (LeanBridges.Counting.choose (0 : ℤ) (3 : ℤ) : ℤ) = 0 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.def_C_3 (n := 0) (k := (3 : ℤ))) (by parley_side) | (have h := (Parley.Items.Stdlib.Counting.def_C_3 (n := 0) (k := (3 : ℤ))) (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_C_3 (n := 0) (k := (3 : ℤ))) (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Counting.def_C_3 (n := 0) (k := (3 : ℤ))) (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Counting.def_C_3 (n := 0) (k := (3 : ℤ))) (by parley_side)).symm | (have h := (Parley.Items.Stdlib.Counting.def_C_3 (n := 0) (k := (3 : ℤ))) (by parley_side); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_C_3 (n := 0) (k := (3 : ℤ))) (by parley_side); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_C_3 (n := 0) (k := (3 : ℤ))) (by parley_side); parley_int_power h) | (have h := (Parley.Items.Stdlib.Counting.def_C_3 (n := 0) (k := (3 : ℤ))) (by parley_side); parley_side)
      -- 1.3. calculation
      have s1_3 : 6 * (LeanBridges.Counting.choose (0 : ℤ) (3 : ℤ) : ℤ) = 0 * (0 - 1) * (0 - 2) := by
        calc 6 * (LeanBridges.Counting.choose (0 : ℤ) (3 : ℤ) : ℤ) = 6 * 0 := by parley_subst s1_2
          _ = 0 * (0 - 1) * (0 - 2) := by norm_num
      all_goals parley_side
    | succ j hIH =>
      -- 1.4. thm:pascal n := j, k := 3
      have s1_4 : (LeanBridges.Counting.choose (j : ℤ) (3 : ℤ) : ℤ) + (LeanBridges.Counting.choose (j : ℤ) (3 - 1 : ℤ) : ℤ) = (LeanBridges.Counting.choose ((j : ℤ) + 1) (3 : ℤ) : ℤ) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.thm_pascal (n := j) (k := (3 : ℤ))) | (have h := (Parley.Items.Stdlib.Counting.thm_pascal (n := j) (k := (3 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.thm_pascal (n := j) (k := (3 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Counting.thm_pascal (n := j) (k := (3 : ℤ))) | exact_mod_cast ((Parley.Items.Stdlib.Counting.thm_pascal (n := j) (k := (3 : ℤ)))).symm | (have h := (Parley.Items.Stdlib.Counting.thm_pascal (n := j) (k := (3 : ℤ))); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.thm_pascal (n := j) (k := (3 : ℤ))); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.thm_pascal (n := j) (k := (3 : ℤ))); parley_int_power h) | (have h := (Parley.Items.Stdlib.Counting.thm_pascal (n := j) (k := (3 : ℤ))); parley_side)
      -- 1.5. substitute 3 − 1 = 2 (arithmetic) into line 1.4
      have s1_5 : (LeanBridges.Counting.choose (j : ℤ) (3 : ℤ) : ℤ) + (LeanBridges.Counting.choose (j : ℤ) (2 : ℤ) : ℤ) = (LeanBridges.Counting.choose ((j : ℤ) + 1) (3 : ℤ) : ℤ) := by parley_subst_at (show (3 - 1 : ℤ) = 2 by parley_side) s1_4
      -- 1.6. thm:binomial-of-two m := j
      have s1_6 : 2 * (LeanBridges.Counting.choose (j : ℤ) (2 : ℤ) : ℤ) = (j : ℤ) * ((j : ℤ) - 1) := by first | linear_combination (norm := parley_norm) (Parley.Proofs.Hammack.BinomialOfTwo.BinomialOfTwo.binomial_of_two (m := j)) | (have h := (Parley.Proofs.Hammack.BinomialOfTwo.BinomialOfTwo.binomial_of_two (m := j)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Hammack.BinomialOfTwo.BinomialOfTwo.binomial_of_two (m := j)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Proofs.Hammack.BinomialOfTwo.BinomialOfTwo.binomial_of_two (m := j)) | exact_mod_cast ((Parley.Proofs.Hammack.BinomialOfTwo.BinomialOfTwo.binomial_of_two (m := j))).symm | (have h := (Parley.Proofs.Hammack.BinomialOfTwo.BinomialOfTwo.binomial_of_two (m := j)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Hammack.BinomialOfTwo.BinomialOfTwo.binomial_of_two (m := j)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Hammack.BinomialOfTwo.BinomialOfTwo.binomial_of_two (m := j)); parley_int_power h) | (have h := (Parley.Proofs.Hammack.BinomialOfTwo.BinomialOfTwo.binomial_of_two (m := j)); parley_side)
      -- 1.7. algebra, from IH, 1.5, 1.6
      have s1_7 : 6 * (LeanBridges.Counting.choose ((j : ℤ) + 1) (3 : ℤ) : ℤ) = ((j : ℤ) + 1) * ((j : ℤ) + 1 - 1) * ((j : ℤ) + 1 - 2) := by linear_combination (norm := parley_norm) hIH + (-6) * s1_5 + (3) * s1_6
      all_goals parley_side
  -- 2. instantiate j := m in line 1
  have s2 : 6 * (LeanBridges.Counting.choose (m : ℤ) (3 : ℤ) : ℤ) = (m : ℤ) * ((m : ℤ) - 1) * ((m : ℤ) - 2) := by first | linear_combination (norm := parley_norm) (s1 m) | (have h := (s1 m); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (s1 m); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (s1 m) | exact_mod_cast ((s1 m)).symm | (have h := (s1 m); rify; linear_combination (norm := parley_norm) h) | (have h := (s1 m); qify; linear_combination (norm := parley_norm) h) | (have h := (s1 m); parley_int_power h) | (have h := (s1 m); parley_side)
  all_goals parley_side

end Parley.Proofs.Hammack.BinomialOfThree.BinomialOfThree
