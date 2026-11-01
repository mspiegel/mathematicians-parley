module

public import Parley.Items.Stdlib.Counting
public import Parley.Library
public import Parley.Proofs.Setmm.ChooseTwoPairs.ChooseTwoPairs

/-! Written from proofs/hammack/choose-two-even.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.ChooseTwoEven.ChooseTwoFormula

theorem choose_two_formula (n : ℕ) :
    (Parley.Library.choose (n : ℤ) (2 : ℤ) : ℚ) = (n : ℚ) * ((n : ℚ) - 1) / 2 := by
  -- 1. induction on k starting at 0
  have s1 : ∀ k : ℕ, (Parley.Library.choose (k : ℤ) (2 : ℤ) : ℚ) = (k : ℚ) * ((k : ℚ) - 1) / 2 := by
    intro k
    induction k with
    | zero =>
      -- 1.1. arithmetic
      have s1_1 : (0 : ℤ) < 2 := by parley_arith
      -- 1.2. calculation
      have s1_2 : (Parley.Library.choose (0 : ℤ) (2 : ℤ) : ℚ) = 0 * (0 - 1) / 2 := by
        calc (Parley.Library.choose (0 : ℤ) (2 : ℤ) : ℚ) = 0 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.def_C_3 (n := 0) (k := (2 : ℤ))) (by parley_side) | (have h := (Parley.Items.Stdlib.Counting.def_C_3 (n := 0) (k := (2 : ℤ))) (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | exact_mod_cast (Parley.Items.Stdlib.Counting.def_C_3 (n := 0) (k := (2 : ℤ))) (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Counting.def_C_3 (n := 0) (k := (2 : ℤ))) (by parley_side)).symm
          _ = 0 * (0 - 1) / 2 := by norm_num
      all_goals parley_side
    | succ k hIH =>
      -- 1.3. calculation
      have s1_3 : (Parley.Library.choose ((k : ℤ) + 1) (2 : ℤ) : ℚ) = ((k : ℚ) + 1) * ((k : ℚ) + 1 - 1) / 2 := by
        calc (Parley.Library.choose ((k : ℤ) + 1) (2 : ℤ) : ℚ) = (k : ℚ) + (Parley.Library.choose (k : ℤ) (2 : ℤ) : ℚ) := by first | linear_combination (norm := parley_norm) (Parley.Proofs.Setmm.ChooseTwoPairs.ChooseTwoPairs.choose_two_pairs (n := k)) | (have h := (Parley.Proofs.Setmm.ChooseTwoPairs.ChooseTwoPairs.choose_two_pairs (n := k)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | exact_mod_cast (Parley.Proofs.Setmm.ChooseTwoPairs.ChooseTwoPairs.choose_two_pairs (n := k)) | exact_mod_cast ((Parley.Proofs.Setmm.ChooseTwoPairs.ChooseTwoPairs.choose_two_pairs (n := k))).symm
          _ = (k : ℚ) + (k : ℚ) * ((k : ℚ) - 1) / 2 := by parley_subst hIH
          _ = ((k : ℚ) + 1) * ((k : ℚ) + 1 - 1) / 2 := by parley_ring
      all_goals parley_side
  -- 2. instantiate k := n in line 1
  have s2 : (Parley.Library.choose (n : ℤ) (2 : ℤ) : ℚ) = (n : ℚ) * ((n : ℚ) - 1) / 2 := by first | linear_combination (norm := parley_norm) (s1 n) | (have h := (s1 n); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | exact_mod_cast (s1 n) | exact_mod_cast ((s1 n)).symm
  all_goals parley_side

end Parley.Proofs.Hammack.ChooseTwoEven.ChooseTwoFormula
