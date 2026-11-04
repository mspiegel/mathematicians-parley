module

public import AlgebraTactics
public import Counting
public import OrderTactics
public import PowerTactics
public import SubstTactics
public import Tactics
public import Parley.Items.Stdlib.Counting

/-! Written from proofs/hammack/binomial-on-the-diagonal.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.BinomialOnTheDiagonal.BinomialOnTheDiagonal

theorem binomial_on_the_diagonal (m : ℕ) :
    (LeanBridges.Counting.choose (m : ℤ) (m : ℤ) : ℤ) = 1 := by
  -- 1. induction on j starting at 0
  have s1 : ∀ j : ℕ, (LeanBridges.Counting.choose (j : ℤ) (j : ℤ) : ℤ) = 1 := by
    intro j
    induction j with
    | zero =>
      -- 1.1. mun:binomial-zero-index n := 0
      have s1_1 : (LeanBridges.Counting.choose (0 : ℤ) (0 : ℤ) : ℤ) = 1 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := 0)) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := 0)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := 0)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := 0)) | exact_mod_cast ((Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := 0))).symm | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := 0)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := 0)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := 0)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := 0)); parley_side)
      all_goals parley_side
    | succ j hIH =>
      -- 1.2. inequalities
      have s1_2 : (j : ℤ) < (j : ℤ) + 1 := by parley_order
      -- 1.3. def:C n := j, k := j + 1, from 1.2
      have s1_3 : (LeanBridges.Counting.choose (j : ℤ) ((j : ℤ) + 1) : ℤ) = 0 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.def_C_3 (n := j) (k := (j : ℤ) + 1)) (by parley_side) | (have h := (Parley.Items.Stdlib.Counting.def_C_3 (n := j) (k := (j : ℤ) + 1)) (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_C_3 (n := j) (k := (j : ℤ) + 1)) (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Counting.def_C_3 (n := j) (k := (j : ℤ) + 1)) (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Counting.def_C_3 (n := j) (k := (j : ℤ) + 1)) (by parley_side)).symm | (have h := (Parley.Items.Stdlib.Counting.def_C_3 (n := j) (k := (j : ℤ) + 1)) (by parley_side); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_C_3 (n := j) (k := (j : ℤ) + 1)) (by parley_side); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_C_3 (n := j) (k := (j : ℤ) + 1)) (by parley_side); parley_int_power h) | (have h := (Parley.Items.Stdlib.Counting.def_C_3 (n := j) (k := (j : ℤ) + 1)) (by parley_side); parley_side)
      -- 1.4. thm:pascal n := j, k := j + 1
      have s1_4 : (LeanBridges.Counting.choose (j : ℤ) ((j : ℤ) + 1) : ℤ) + (LeanBridges.Counting.choose (j : ℤ) ((j : ℤ) + 1 - 1) : ℤ) = (LeanBridges.Counting.choose ((j : ℤ) + 1) ((j : ℤ) + 1) : ℤ) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.thm_pascal (n := j) (k := (j : ℤ) + 1)) | (have h := (Parley.Items.Stdlib.Counting.thm_pascal (n := j) (k := (j : ℤ) + 1)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.thm_pascal (n := j) (k := (j : ℤ) + 1)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Counting.thm_pascal (n := j) (k := (j : ℤ) + 1)) | exact_mod_cast ((Parley.Items.Stdlib.Counting.thm_pascal (n := j) (k := (j : ℤ) + 1))).symm | (have h := (Parley.Items.Stdlib.Counting.thm_pascal (n := j) (k := (j : ℤ) + 1)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.thm_pascal (n := j) (k := (j : ℤ) + 1)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.thm_pascal (n := j) (k := (j : ℤ) + 1)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Counting.thm_pascal (n := j) (k := (j : ℤ) + 1)); parley_side)
      -- 1.5. substitute
      have s1_5 : (LeanBridges.Counting.choose (j : ℤ) ((j : ℤ) + 1) : ℤ) + (LeanBridges.Counting.choose (j : ℤ) (j : ℤ) : ℤ) = (LeanBridges.Counting.choose ((j : ℤ) + 1) ((j : ℤ) + 1) : ℤ) := by
        have c1 : (j : ℤ) + 1 - 1 = (j : ℤ) := by parley_ring
        have row1 : (LeanBridges.Counting.choose (j : ℤ) ((j : ℤ) + 1) : ℤ) + (LeanBridges.Counting.choose (j : ℤ) (j : ℤ) : ℤ) = (LeanBridges.Counting.choose ((j : ℤ) + 1) ((j : ℤ) + 1) : ℤ) := by parley_subst_at c1 s1_4
        exact row1
      -- 1.6. calculation
      have s1_6 : (LeanBridges.Counting.choose ((j : ℤ) + 1) ((j : ℤ) + 1) : ℤ) = 1 := by
        calc (LeanBridges.Counting.choose ((j : ℤ) + 1) ((j : ℤ) + 1) : ℤ) = (LeanBridges.Counting.choose (j : ℤ) ((j : ℤ) + 1) : ℤ) + (LeanBridges.Counting.choose (j : ℤ) (j : ℤ) : ℤ) := by parley_side
          _ = 0 + (LeanBridges.Counting.choose (j : ℤ) (j : ℤ) : ℤ) := by parley_subst s1_3
          _ = 0 + 1 := by parley_subst hIH
          _ = 1 := by norm_num
      all_goals parley_side
  -- 2. instantiate j := m in line 1
  have s2 : (LeanBridges.Counting.choose (m : ℤ) (m : ℤ) : ℤ) = 1 := by first | linear_combination (norm := parley_norm) (s1 m) | (have h := (s1 m); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (s1 m); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (s1 m) | exact_mod_cast ((s1 m)).symm | (have h := (s1 m); rify; linear_combination (norm := parley_norm) h) | (have h := (s1 m); qify; linear_combination (norm := parley_norm) h) | (have h := (s1 m); parley_int_power h) | (have h := (s1 m); parley_side)
  all_goals exact s2

end Parley.Proofs.Hammack.BinomialOnTheDiagonal.BinomialOnTheDiagonal
