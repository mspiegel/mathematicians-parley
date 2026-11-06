module

public import AlgebraTactics
public import Counting
public import FactorialTactics
public import PowerTactics
public import SubstTactics
public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Parley.Items.Stdlib.Counting
public import Parley.Proofs.Setmm.ChooseTwoPairs.ChooseOne

/-! Written from proofs/setmm/choose-two-pairs.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.ChooseTwoPairs.ChooseTwoPairs

theorem choose_two_pairs (n : ℤ) (hH1 : 0 ≤ n) :
    n + (LeanBridges.Counting.choose n (2 : ℤ) : ℤ) = (LeanBridges.Counting.choose (n + 1) (2 : ℤ) : ℤ) := by
  -- 1. thm:pascal k := 2
  have s1 : (LeanBridges.Counting.choose n (2 : ℤ) : ℤ) + (LeanBridges.Counting.choose n (2 - 1 : ℤ) : ℤ) = (LeanBridges.Counting.choose (n + 1) (2 : ℤ) : ℤ) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.thm_pascal (n := n) (by parley_side) (k := (2 : ℤ))) | (have h := (Parley.Items.Stdlib.Counting.thm_pascal (n := n) (by parley_side) (k := (2 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.thm_pascal (n := n) (by parley_side) (k := (2 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Counting.thm_pascal (n := n) (by parley_side) (k := (2 : ℤ))) | exact_mod_cast ((Parley.Items.Stdlib.Counting.thm_pascal (n := n) (by parley_side) (k := (2 : ℤ)))).symm | (have h := (Parley.Items.Stdlib.Counting.thm_pascal (n := n) (by parley_side) (k := (2 : ℤ))); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.thm_pascal (n := n) (by parley_side) (k := (2 : ℤ))); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.thm_pascal (n := n) (by parley_side) (k := (2 : ℤ))); parley_int_power h) | (have h := (Parley.Items.Stdlib.Counting.thm_pascal (n := n) (by parley_side) (k := (2 : ℤ))); parley_side)
  -- 2. substitute 2 − 1 = 1 (arithmetic) into line 1
  have s2 : (LeanBridges.Counting.choose n (2 : ℤ) : ℤ) + (LeanBridges.Counting.choose n (1 : ℤ) : ℤ) = (LeanBridges.Counting.choose (n + 1) (2 : ℤ) : ℤ) := by parley_subst_at (show (2 - 1 : ℤ) = 1 by parley_side) s1
  -- 3. substitute
  have s3 : (LeanBridges.Counting.choose n (2 : ℤ) : ℤ) + n = (LeanBridges.Counting.choose (n + 1) (2 : ℤ) : ℤ) := by
    have c1 : (LeanBridges.Counting.choose n (1 : ℤ) : ℤ) = n := by first | linear_combination (norm := parley_norm) (Parley.Proofs.Setmm.ChooseTwoPairs.ChooseOne.choose_one (n := n) (by parley_side)) | (have h := (Parley.Proofs.Setmm.ChooseTwoPairs.ChooseOne.choose_one (n := n) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Setmm.ChooseTwoPairs.ChooseOne.choose_one (n := n) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Proofs.Setmm.ChooseTwoPairs.ChooseOne.choose_one (n := n) (by parley_side)) | exact_mod_cast ((Parley.Proofs.Setmm.ChooseTwoPairs.ChooseOne.choose_one (n := n) (by parley_side))).symm | (have h := (Parley.Proofs.Setmm.ChooseTwoPairs.ChooseOne.choose_one (n := n) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Setmm.ChooseTwoPairs.ChooseOne.choose_one (n := n) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Setmm.ChooseTwoPairs.ChooseOne.choose_one (n := n) (by parley_side)); parley_int_power h) | (have h := (Parley.Proofs.Setmm.ChooseTwoPairs.ChooseOne.choose_one (n := n) (by parley_side)); parley_side)
    have row1 : (LeanBridges.Counting.choose n (2 : ℤ) : ℤ) + n = (LeanBridges.Counting.choose (n + 1) (2 : ℤ) : ℤ) := by parley_subst_at c1 s2
    exact row1
  -- 4. calculation
  have s4 : n + (LeanBridges.Counting.choose n (2 : ℤ) : ℤ) = (LeanBridges.Counting.choose (n + 1) (2 : ℤ) : ℤ) := by
    calc n + (LeanBridges.Counting.choose n (2 : ℤ) : ℤ) = (LeanBridges.Counting.choose n (2 : ℤ) : ℤ) + n := by parley_ring
      _ = (LeanBridges.Counting.choose (n + 1) (2 : ℤ) : ℤ) := by parley_side
  all_goals exact s4

end Parley.Proofs.Setmm.ChooseTwoPairs.ChooseTwoPairs
