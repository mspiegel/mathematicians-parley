module

public import Parley.Items.Stdlib.Counting
public import Parley.Library

/-! Written from proofs/hammack/binomial-on-the-diagonal.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.BinomialOnTheDiagonal.BinomialOnTheDiagonal

theorem binomial_on_the_diagonal (m : ℕ) :
    (Parley.Library.choose (m : ℤ) (m : ℤ) : ℤ) = 1 := by
  -- 1. induction on j starting at 0
  have s1 : ∀ j : ℕ, (Parley.Library.choose (j : ℤ) (j : ℤ) : ℤ) = 1 := by
    intro j
    induction j with
    | zero =>
      -- 1.1. mun:binomial-zero-index n := 0
      have s1_1 : (Parley.Library.choose (0 : ℤ) (0 : ℤ) : ℤ) = 1 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := 0)) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := 0)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | exact_mod_cast (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := 0)) | exact_mod_cast ((Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := 0))).symm
      all_goals parley_side
    | succ j hIH =>
      -- 1.2. inequalities
      have s1_2 : (j : ℤ) < (j : ℤ) + 1 := by parley_side
      -- 1.3. def:C n := j, k := j + 1, from 1.2
      have s1_3 : (Parley.Library.choose (j : ℤ) ((j : ℤ) + 1) : ℤ) = 0 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.def_C_3 (n := j) (k := (j : ℤ) + 1)) (by parley_side) | (have h := (Parley.Items.Stdlib.Counting.def_C_3 (n := j) (k := (j : ℤ) + 1)) (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | exact_mod_cast (Parley.Items.Stdlib.Counting.def_C_3 (n := j) (k := (j : ℤ) + 1)) (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Counting.def_C_3 (n := j) (k := (j : ℤ) + 1)) (by parley_side)).symm
      -- 1.4. thm:pascal n := j, k := j + 1
      have s1_4 : (Parley.Library.choose (j : ℤ) ((j : ℤ) + 1) : ℤ) + (Parley.Library.choose (j : ℤ) ((j : ℤ) + 1 - 1) : ℤ) = (Parley.Library.choose ((j : ℤ) + 1) ((j : ℤ) + 1) : ℤ) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.thm_pascal (n := j) (k := (j : ℤ) + 1)) | (have h := (Parley.Items.Stdlib.Counting.thm_pascal (n := j) (k := (j : ℤ) + 1)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | exact_mod_cast (Parley.Items.Stdlib.Counting.thm_pascal (n := j) (k := (j : ℤ) + 1)) | exact_mod_cast ((Parley.Items.Stdlib.Counting.thm_pascal (n := j) (k := (j : ℤ) + 1))).symm
      -- 1.5. substitute
      have s1_5 : (Parley.Library.choose (j : ℤ) ((j : ℤ) + 1) : ℤ) + (Parley.Library.choose (j : ℤ) (j : ℤ) : ℤ) = (Parley.Library.choose ((j : ℤ) + 1) ((j : ℤ) + 1) : ℤ) := by
        have c1 : (j : ℤ) + 1 - 1 = (j : ℤ) := by parley_ring
        have row1 : (Parley.Library.choose (j : ℤ) ((j : ℤ) + 1) : ℤ) + (Parley.Library.choose (j : ℤ) (j : ℤ) : ℤ) = (Parley.Library.choose ((j : ℤ) + 1) ((j : ℤ) + 1) : ℤ) := by parley_subst_at c1 s1_4
        exact row1
      -- 1.6. calculation
      have s1_6 : (Parley.Library.choose ((j : ℤ) + 1) ((j : ℤ) + 1) : ℤ) = 1 := by
        calc (Parley.Library.choose ((j : ℤ) + 1) ((j : ℤ) + 1) : ℤ) = (Parley.Library.choose (j : ℤ) ((j : ℤ) + 1) : ℤ) + (Parley.Library.choose (j : ℤ) (j : ℤ) : ℤ) := by parley_side
          _ = 0 + (Parley.Library.choose (j : ℤ) (j : ℤ) : ℤ) := by parley_subst s1_3
          _ = 0 + 1 := by parley_subst hIH
          _ = 1 := by norm_num
      all_goals parley_side
  -- 2. instantiate j := m in line 1
  have s2 : (Parley.Library.choose (m : ℤ) (m : ℤ) : ℤ) = 1 := by first | linear_combination (norm := parley_norm) (s1 m) | (have h := (s1 m); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | exact_mod_cast (s1 m) | exact_mod_cast ((s1 m)).symm
  all_goals parley_side

end Parley.Proofs.Hammack.BinomialOnTheDiagonal.BinomialOnTheDiagonal
