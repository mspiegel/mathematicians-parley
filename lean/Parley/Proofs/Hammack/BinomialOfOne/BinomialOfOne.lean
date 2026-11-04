module

public import ArithTactics
public import Counting
public import PowerTactics
public import SubstTactics
public import Tactics
public import Parley.Items.Stdlib.Counting

/-! Written from proofs/hammack/binomial-of-one.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.BinomialOfOne.BinomialOfOne

theorem binomial_of_one (m : ℕ) :
    (LeanBridges.Counting.choose (m : ℤ) (1 : ℤ) : ℤ) = (m : ℤ) := by
  -- 1. induction on j starting at 0
  have s1 : ∀ j : ℕ, (LeanBridges.Counting.choose (j : ℤ) (1 : ℤ) : ℤ) = (j : ℤ) := by
    intro j
    induction j with
    | zero =>
      -- 1.1. arithmetic
      have s1_1 : (0 : ℤ) < 1 := by parley_arith
      -- 1.2. def:C n := 0, k := 1, from 1.1
      have s1_2 : (LeanBridges.Counting.choose (0 : ℤ) (1 : ℤ) : ℤ) = 0 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.def_C_3 (n := 0) (k := (1 : ℤ))) (by parley_side) | (have h := (Parley.Items.Stdlib.Counting.def_C_3 (n := 0) (k := (1 : ℤ))) (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_C_3 (n := 0) (k := (1 : ℤ))) (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Counting.def_C_3 (n := 0) (k := (1 : ℤ))) (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Counting.def_C_3 (n := 0) (k := (1 : ℤ))) (by parley_side)).symm | (have h := (Parley.Items.Stdlib.Counting.def_C_3 (n := 0) (k := (1 : ℤ))) (by parley_side); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_C_3 (n := 0) (k := (1 : ℤ))) (by parley_side); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_C_3 (n := 0) (k := (1 : ℤ))) (by parley_side); parley_int_power h) | (have h := (Parley.Items.Stdlib.Counting.def_C_3 (n := 0) (k := (1 : ℤ))) (by parley_side); parley_side)
      all_goals parley_side
    | succ j hIH =>
      -- 1.3. thm:pascal n := j, k := 1
      have s1_3 : (LeanBridges.Counting.choose (j : ℤ) (1 : ℤ) : ℤ) + (LeanBridges.Counting.choose (j : ℤ) (1 - 1 : ℤ) : ℤ) = (LeanBridges.Counting.choose ((j : ℤ) + 1) (1 : ℤ) : ℤ) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.thm_pascal (n := j) (k := (1 : ℤ))) | (have h := (Parley.Items.Stdlib.Counting.thm_pascal (n := j) (k := (1 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.thm_pascal (n := j) (k := (1 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Counting.thm_pascal (n := j) (k := (1 : ℤ))) | exact_mod_cast ((Parley.Items.Stdlib.Counting.thm_pascal (n := j) (k := (1 : ℤ)))).symm | (have h := (Parley.Items.Stdlib.Counting.thm_pascal (n := j) (k := (1 : ℤ))); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.thm_pascal (n := j) (k := (1 : ℤ))); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.thm_pascal (n := j) (k := (1 : ℤ))); parley_int_power h) | (have h := (Parley.Items.Stdlib.Counting.thm_pascal (n := j) (k := (1 : ℤ))); parley_side)
      -- 1.4. mun:binomial-zero-index n := j
      have s1_4 : (LeanBridges.Counting.choose (j : ℤ) (0 : ℤ) : ℤ) = 1 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := j)) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := j)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := j)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := j)) | exact_mod_cast ((Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := j))).symm | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := j)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := j)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := j)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := j)); parley_side)
      -- 1.5. substitute 1 − 1 = 0 (arithmetic) into line 1.3
      have s1_5 : (LeanBridges.Counting.choose (j : ℤ) (1 : ℤ) : ℤ) + (LeanBridges.Counting.choose (j : ℤ) (0 : ℤ) : ℤ) = (LeanBridges.Counting.choose ((j : ℤ) + 1) (1 : ℤ) : ℤ) := by parley_subst_at (show (1 - 1 : ℤ) = 0 by parley_side) s1_3
      -- 1.6. calculation
      have s1_6 : (LeanBridges.Counting.choose ((j : ℤ) + 1) (1 : ℤ) : ℤ) = (j : ℤ) + 1 := by
        calc (LeanBridges.Counting.choose ((j : ℤ) + 1) (1 : ℤ) : ℤ) = (LeanBridges.Counting.choose (j : ℤ) (1 : ℤ) : ℤ) + (LeanBridges.Counting.choose (j : ℤ) (0 : ℤ) : ℤ) := by parley_side
          _ = (j : ℤ) + (LeanBridges.Counting.choose (j : ℤ) (0 : ℤ) : ℤ) := by parley_subst hIH
          _ = (j : ℤ) + 1 := by parley_subst s1_4
      all_goals parley_side
  -- 2. instantiate j := m in line 1
  have s2 : (LeanBridges.Counting.choose (m : ℤ) (1 : ℤ) : ℤ) = (m : ℤ) := by first | linear_combination (norm := parley_norm) (s1 m) | (have h := (s1 m); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (s1 m); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (s1 m) | exact_mod_cast ((s1 m)).symm | (have h := (s1 m); rify; linear_combination (norm := parley_norm) h) | (have h := (s1 m); qify; linear_combination (norm := parley_norm) h) | (have h := (s1 m); parley_int_power h) | (have h := (s1 m); parley_side)
  all_goals exact s2

end Parley.Proofs.Hammack.BinomialOfOne.BinomialOfOne
