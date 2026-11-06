module

public import ArithTactics
public import Counting
public import FactorialTactics
public import Functions
public import PowerTactics
public import SubstTactics
public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Parley.Items.Stdlib.Counting
public import Parley.Proofs.Hammack.BinomialOfOne.BinomialOfOne

/-! Written from proofs/hammack/binomial-of-two.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.BinomialOfTwo.BinomialOfTwo

theorem binomial_of_two (m : ℤ) (hH1 : 0 ≤ m) :
    2 * (LeanBridges.Counting.choose m (2 : ℤ) : ℤ) = m * (m - 1) := by
  -- 1. induction on j starting at 0
  have s1 : ∀ j : ℤ, 0 ≤ j → 2 * (LeanBridges.Counting.choose j (2 : ℤ) : ℤ) = j * (j - 1) := by
    intro j h_j
    replace h_j : 0 ≤ j := by omega
    induction j, h_j using LeanBridges.Functions.le_induction with
    | base =>
      -- 1.1. arithmetic
      have s1_1 : (0 : ℤ) < 2 := by parley_arith
      -- 1.2. def:C n := 0, k := 2, from 1.1
      have s1_2 : (LeanBridges.Counting.choose (0 : ℤ) (2 : ℤ) : ℤ) = 0 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.def_C_3 (n := (0 : ℤ)) (by parley_side) (k := (2 : ℤ))) (by parley_side) | (have h := (Parley.Items.Stdlib.Counting.def_C_3 (n := (0 : ℤ)) (by parley_side) (k := (2 : ℤ))) (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_C_3 (n := (0 : ℤ)) (by parley_side) (k := (2 : ℤ))) (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Counting.def_C_3 (n := (0 : ℤ)) (by parley_side) (k := (2 : ℤ))) (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Counting.def_C_3 (n := (0 : ℤ)) (by parley_side) (k := (2 : ℤ))) (by parley_side)).symm | (have h := (Parley.Items.Stdlib.Counting.def_C_3 (n := (0 : ℤ)) (by parley_side) (k := (2 : ℤ))) (by parley_side); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_C_3 (n := (0 : ℤ)) (by parley_side) (k := (2 : ℤ))) (by parley_side); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_C_3 (n := (0 : ℤ)) (by parley_side) (k := (2 : ℤ))) (by parley_side); parley_int_power h) | (have h := (Parley.Items.Stdlib.Counting.def_C_3 (n := (0 : ℤ)) (by parley_side) (k := (2 : ℤ))) (by parley_side); parley_side)
      -- 1.3. calculation
      have s1_3 : 2 * (LeanBridges.Counting.choose (0 : ℤ) (2 : ℤ) : ℤ) = 0 * (0 - 1) := by
        calc 2 * (LeanBridges.Counting.choose (0 : ℤ) (2 : ℤ) : ℤ) = 2 * 0 := by parley_subst s1_2
          _ = 0 * (0 - 1) := by norm_num
      all_goals parley_side
    | succ j hK hIH =>
      -- 1.4. thm:pascal n := j, k := 2
      have s1_4 : (LeanBridges.Counting.choose j (2 : ℤ) : ℤ) + (LeanBridges.Counting.choose j (2 - 1 : ℤ) : ℤ) = (LeanBridges.Counting.choose (j + 1) (2 : ℤ) : ℤ) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.thm_pascal (n := j) (by parley_side) (k := (2 : ℤ))) | (have h := (Parley.Items.Stdlib.Counting.thm_pascal (n := j) (by parley_side) (k := (2 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.thm_pascal (n := j) (by parley_side) (k := (2 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Counting.thm_pascal (n := j) (by parley_side) (k := (2 : ℤ))) | exact_mod_cast ((Parley.Items.Stdlib.Counting.thm_pascal (n := j) (by parley_side) (k := (2 : ℤ)))).symm | (have h := (Parley.Items.Stdlib.Counting.thm_pascal (n := j) (by parley_side) (k := (2 : ℤ))); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.thm_pascal (n := j) (by parley_side) (k := (2 : ℤ))); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.thm_pascal (n := j) (by parley_side) (k := (2 : ℤ))); parley_int_power h) | (have h := (Parley.Items.Stdlib.Counting.thm_pascal (n := j) (by parley_side) (k := (2 : ℤ))); parley_side)
      -- 1.5. substitute 2 − 1 = 1 (arithmetic) into line 1.4
      have s1_5 : (LeanBridges.Counting.choose j (2 : ℤ) : ℤ) + (LeanBridges.Counting.choose j (1 : ℤ) : ℤ) = (LeanBridges.Counting.choose (j + 1) (2 : ℤ) : ℤ) := by parley_subst_at (show (2 - 1 : ℤ) = 1 by parley_side) s1_4
      -- 1.6. thm:binomial-of-one m := j
      have s1_6 : (LeanBridges.Counting.choose j (1 : ℤ) : ℤ) = j := by first | linear_combination (norm := parley_norm) (Parley.Proofs.Hammack.BinomialOfOne.BinomialOfOne.binomial_of_one (m := j) (by parley_side)) | (have h := (Parley.Proofs.Hammack.BinomialOfOne.BinomialOfOne.binomial_of_one (m := j) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Hammack.BinomialOfOne.BinomialOfOne.binomial_of_one (m := j) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Proofs.Hammack.BinomialOfOne.BinomialOfOne.binomial_of_one (m := j) (by parley_side)) | exact_mod_cast ((Parley.Proofs.Hammack.BinomialOfOne.BinomialOfOne.binomial_of_one (m := j) (by parley_side))).symm | (have h := (Parley.Proofs.Hammack.BinomialOfOne.BinomialOfOne.binomial_of_one (m := j) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Hammack.BinomialOfOne.BinomialOfOne.binomial_of_one (m := j) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Hammack.BinomialOfOne.BinomialOfOne.binomial_of_one (m := j) (by parley_side)); parley_int_power h) | (have h := (Parley.Proofs.Hammack.BinomialOfOne.BinomialOfOne.binomial_of_one (m := j) (by parley_side)); parley_side)
      -- 1.7. algebra, from IH, 1.5, 1.6
      have s1_7 : 2 * (LeanBridges.Counting.choose (j + 1) (2 : ℤ) : ℤ) = (j + 1) * (j + 1 - 1) := by linear_combination (norm := parley_norm) hIH + (-2) * s1_5 + (2) * s1_6
      all_goals parley_side
  -- 2. instantiate j := m in line 1
  have s2 : 2 * (LeanBridges.Counting.choose m (2 : ℤ) : ℤ) = m * (m - 1) := by first | linear_combination (norm := parley_norm) (s1 m (by parley_side)) | (have h := (s1 m (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (s1 m (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (s1 m (by parley_side)) | exact_mod_cast ((s1 m (by parley_side))).symm | (have h := (s1 m (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (s1 m (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (s1 m (by parley_side)); parley_int_power h) | (have h := (s1 m (by parley_side)); parley_side)
  all_goals exact s2

end Parley.Proofs.Hammack.BinomialOfTwo.BinomialOfTwo
