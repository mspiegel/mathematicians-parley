module

public import Parley.Items.Stdlib.Counting
public import Parley.Library

/-! Written from proofs/setmm/choose-two-pairs.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.ChooseTwoPairs.ChooseOne

theorem choose_one (n : ℕ) :
    (Parley.Library.choose (n : ℤ) (1 : ℤ) : ℤ) = (n : ℤ) := by
  -- 1. induction on k starting at 0
  have s1 : ∀ k : ℕ, (Parley.Library.choose (k : ℤ) (1 : ℤ) : ℤ) = (k : ℤ) := by
    intro k
    induction k with
    | zero =>
      -- 1.1. arithmetic
      have s1_1 : (0 : ℤ) < 1 := by parley_arith
      -- 1.2. def:C n := 0, k := 1, from 1.1
      have s1_2 : (Parley.Library.choose (0 : ℤ) (1 : ℤ) : ℤ) = 0 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.def_C_3 (n := 0) (k := (1 : ℤ))) (by parley_side) | (have h := (Parley.Items.Stdlib.Counting.def_C_3 (n := 0) (k := (1 : ℤ))) (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | exact_mod_cast (Parley.Items.Stdlib.Counting.def_C_3 (n := 0) (k := (1 : ℤ))) (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Counting.def_C_3 (n := 0) (k := (1 : ℤ))) (by parley_side)).symm
      all_goals parley_side
    | succ k hIH =>
      -- 1.3. thm:pascal n := k, k := 1
      have s1_3 : (Parley.Library.choose (k : ℤ) (1 : ℤ) : ℤ) + (Parley.Library.choose (k : ℤ) (1 - 1 : ℤ) : ℤ) = (Parley.Library.choose ((k : ℤ) + 1) (1 : ℤ) : ℤ) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.thm_pascal (n := k) (k := (1 : ℤ))) | (have h := (Parley.Items.Stdlib.Counting.thm_pascal (n := k) (k := (1 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | exact_mod_cast (Parley.Items.Stdlib.Counting.thm_pascal (n := k) (k := (1 : ℤ))) | exact_mod_cast ((Parley.Items.Stdlib.Counting.thm_pascal (n := k) (k := (1 : ℤ)))).symm
      -- 1.4. substitute 1 − 1 = 0 (arithmetic) into line 1.3
      have s1_4 : (Parley.Library.choose (k : ℤ) (1 : ℤ) : ℤ) + (Parley.Library.choose (k : ℤ) (0 : ℤ) : ℤ) = (Parley.Library.choose ((k : ℤ) + 1) (1 : ℤ) : ℤ) := by parley_subst_at (show (1 - 1 : ℤ) = 0 by parley_side) s1_3
      -- 1.5. substitute
      have s1_5 : (Parley.Library.choose (k : ℤ) (1 : ℤ) : ℤ) + 1 = (Parley.Library.choose ((k : ℤ) + 1) (1 : ℤ) : ℤ) := by
        have c1 : (Parley.Library.choose (k : ℤ) (0 : ℤ) : ℤ) = 1 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := k)) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := k)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | exact_mod_cast (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := k)) | exact_mod_cast ((Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := k))).symm
        have row1 : (Parley.Library.choose (k : ℤ) (1 : ℤ) : ℤ) + 1 = (Parley.Library.choose ((k : ℤ) + 1) (1 : ℤ) : ℤ) := by parley_subst_at c1 s1_4
        exact row1
      -- 1.6. calculation
      have s1_6 : (Parley.Library.choose ((k : ℤ) + 1) (1 : ℤ) : ℤ) = (k : ℤ) + 1 := by
        calc (Parley.Library.choose ((k : ℤ) + 1) (1 : ℤ) : ℤ) = (Parley.Library.choose (k : ℤ) (1 : ℤ) : ℤ) + 1 := by parley_side
          _ = (k : ℤ) + 1 := by parley_subst hIH
      all_goals parley_side
  -- 2. instantiate k := n in line 1
  have s2 : (Parley.Library.choose (n : ℤ) (1 : ℤ) : ℤ) = (n : ℤ) := by first | linear_combination (norm := parley_norm) (s1 n) | (have h := (s1 n); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | exact_mod_cast (s1 n) | exact_mod_cast ((s1 n)).symm
  all_goals parley_side

end Parley.Proofs.Setmm.ChooseTwoPairs.ChooseOne
