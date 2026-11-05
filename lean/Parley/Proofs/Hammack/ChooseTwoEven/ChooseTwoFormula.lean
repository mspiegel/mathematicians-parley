module

public import AlgebraTactics
public import ArithTactics
public import Counting
public import FactorialTactics
public import PowerTactics
public import SubstTactics
public import Tactics
public import Parley.Items.Stdlib.Counting
public import Parley.Proofs.Setmm.ChooseTwoPairs.ChooseTwoPairs

/-! Written from proofs/hammack/choose-two-even.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.ChooseTwoEven.ChooseTwoFormula

theorem choose_two_formula (n : ℕ) :
    (LeanBridges.Counting.choose (n : ℤ) (2 : ℤ) : ℚ) = (n : ℚ) * ((n : ℚ) - 1) / 2 := by
  -- 1. induction on k starting at 0
  have s1 : ∀ k : ℕ, (LeanBridges.Counting.choose (k : ℤ) (2 : ℤ) : ℚ) = (k : ℚ) * ((k : ℚ) - 1) / 2 := by
    intro k
    induction k with
    | zero =>
      -- 1.1. arithmetic
      have s1_1 : (0 : ℤ) < 2 := by parley_arith
      -- 1.2. calculation
      have s1_2 : (LeanBridges.Counting.choose (0 : ℤ) (2 : ℤ) : ℚ) = 0 * (0 - 1) / 2 := by
        calc (LeanBridges.Counting.choose (0 : ℤ) (2 : ℤ) : ℚ) = 0 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.def_C_3 (n := 0) (k := (2 : ℤ))) (by parley_side) | (have h := (Parley.Items.Stdlib.Counting.def_C_3 (n := 0) (k := (2 : ℤ))) (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_C_3 (n := 0) (k := (2 : ℤ))) (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Counting.def_C_3 (n := 0) (k := (2 : ℤ))) (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Counting.def_C_3 (n := 0) (k := (2 : ℤ))) (by parley_side)).symm | (have h := (Parley.Items.Stdlib.Counting.def_C_3 (n := 0) (k := (2 : ℤ))) (by parley_side); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_C_3 (n := 0) (k := (2 : ℤ))) (by parley_side); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_C_3 (n := 0) (k := (2 : ℤ))) (by parley_side); parley_int_power h) | (have h := (Parley.Items.Stdlib.Counting.def_C_3 (n := 0) (k := (2 : ℤ))) (by parley_side); parley_side)
          _ = 0 * (0 - 1) / 2 := by norm_num
      all_goals parley_side
    | succ k hIH =>
      -- 1.3. calculation
      have s1_3 : (LeanBridges.Counting.choose ((k : ℤ) + 1) (2 : ℤ) : ℚ) = ((k : ℚ) + 1) * ((k : ℚ) + 1 - 1) / 2 := by
        calc (LeanBridges.Counting.choose ((k : ℤ) + 1) (2 : ℤ) : ℚ) = (k : ℚ) + (LeanBridges.Counting.choose (k : ℤ) (2 : ℤ) : ℚ) := by first | linear_combination (norm := parley_norm) (Parley.Proofs.Setmm.ChooseTwoPairs.ChooseTwoPairs.choose_two_pairs (n := k)) | (have h := (Parley.Proofs.Setmm.ChooseTwoPairs.ChooseTwoPairs.choose_two_pairs (n := k)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Setmm.ChooseTwoPairs.ChooseTwoPairs.choose_two_pairs (n := k)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Proofs.Setmm.ChooseTwoPairs.ChooseTwoPairs.choose_two_pairs (n := k)) | exact_mod_cast ((Parley.Proofs.Setmm.ChooseTwoPairs.ChooseTwoPairs.choose_two_pairs (n := k))).symm | (have h := (Parley.Proofs.Setmm.ChooseTwoPairs.ChooseTwoPairs.choose_two_pairs (n := k)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Setmm.ChooseTwoPairs.ChooseTwoPairs.choose_two_pairs (n := k)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Setmm.ChooseTwoPairs.ChooseTwoPairs.choose_two_pairs (n := k)); parley_int_power h) | (have h := (Parley.Proofs.Setmm.ChooseTwoPairs.ChooseTwoPairs.choose_two_pairs (n := k)); parley_side)
          _ = (k : ℚ) + (k : ℚ) * ((k : ℚ) - 1) / 2 := by parley_subst hIH
          _ = ((k : ℚ) + 1) * ((k : ℚ) + 1 - 1) / 2 := by parley_ring
      all_goals parley_side
  -- 2. instantiate k := n in line 1
  have s2 : (LeanBridges.Counting.choose (n : ℤ) (2 : ℤ) : ℚ) = (n : ℚ) * ((n : ℚ) - 1) / 2 := by first | linear_combination (norm := parley_norm) (s1 n) | (have h := (s1 n); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (s1 n); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (s1 n) | exact_mod_cast ((s1 n)).symm | (have h := (s1 n); rify; linear_combination (norm := parley_norm) h) | (have h := (s1 n); qify; linear_combination (norm := parley_norm) h) | (have h := (s1 n); parley_int_power h) | (have h := (s1 n); parley_side)
  all_goals exact s2

end Parley.Proofs.Hammack.ChooseTwoEven.ChooseTwoFormula
