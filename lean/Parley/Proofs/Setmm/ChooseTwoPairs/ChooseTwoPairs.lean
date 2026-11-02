module

public import LeanBridges
public import Parley.Items.Stdlib.Counting
public import Parley.Proofs.Setmm.ChooseTwoPairs.ChooseOne

/-! Written from proofs/setmm/choose-two-pairs.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.ChooseTwoPairs.ChooseTwoPairs

theorem choose_two_pairs (n : ℕ) :
    (n : ℤ) + (LeanBridges.Counting.choose (n : ℤ) (2 : ℤ) : ℤ) = (LeanBridges.Counting.choose ((n : ℤ) + 1) (2 : ℤ) : ℤ) := by
  -- 1. thm:pascal k := 2
  have s1 : (LeanBridges.Counting.choose (n : ℤ) (2 : ℤ) : ℤ) + (LeanBridges.Counting.choose (n : ℤ) (2 - 1 : ℤ) : ℤ) = (LeanBridges.Counting.choose ((n : ℤ) + 1) (2 : ℤ) : ℤ) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.thm_pascal (n := n) (k := (2 : ℤ))) | (have h := (Parley.Items.Stdlib.Counting.thm_pascal (n := n) (k := (2 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.thm_pascal (n := n) (k := (2 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Counting.thm_pascal (n := n) (k := (2 : ℤ))) | exact_mod_cast ((Parley.Items.Stdlib.Counting.thm_pascal (n := n) (k := (2 : ℤ)))).symm | (have h := (Parley.Items.Stdlib.Counting.thm_pascal (n := n) (k := (2 : ℤ))); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.thm_pascal (n := n) (k := (2 : ℤ))); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.thm_pascal (n := n) (k := (2 : ℤ))); parley_int_power h) | (have h := (Parley.Items.Stdlib.Counting.thm_pascal (n := n) (k := (2 : ℤ))); parley_side)
  -- 2. substitute 2 − 1 = 1 (arithmetic) into line 1
  have s2 : (LeanBridges.Counting.choose (n : ℤ) (2 : ℤ) : ℤ) + (LeanBridges.Counting.choose (n : ℤ) (1 : ℤ) : ℤ) = (LeanBridges.Counting.choose ((n : ℤ) + 1) (2 : ℤ) : ℤ) := by parley_subst_at (show (2 - 1 : ℤ) = 1 by parley_side) s1
  -- 3. substitute
  have s3 : (LeanBridges.Counting.choose (n : ℤ) (2 : ℤ) : ℤ) + (n : ℤ) = (LeanBridges.Counting.choose ((n : ℤ) + 1) (2 : ℤ) : ℤ) := by
    have c1 : (LeanBridges.Counting.choose (n : ℤ) (1 : ℤ) : ℤ) = (n : ℤ) := by first | linear_combination (norm := parley_norm) (Parley.Proofs.Setmm.ChooseTwoPairs.ChooseOne.choose_one (n := n)) | (have h := (Parley.Proofs.Setmm.ChooseTwoPairs.ChooseOne.choose_one (n := n)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Setmm.ChooseTwoPairs.ChooseOne.choose_one (n := n)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Proofs.Setmm.ChooseTwoPairs.ChooseOne.choose_one (n := n)) | exact_mod_cast ((Parley.Proofs.Setmm.ChooseTwoPairs.ChooseOne.choose_one (n := n))).symm | (have h := (Parley.Proofs.Setmm.ChooseTwoPairs.ChooseOne.choose_one (n := n)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Setmm.ChooseTwoPairs.ChooseOne.choose_one (n := n)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Setmm.ChooseTwoPairs.ChooseOne.choose_one (n := n)); parley_int_power h) | (have h := (Parley.Proofs.Setmm.ChooseTwoPairs.ChooseOne.choose_one (n := n)); parley_side)
    have row1 : (LeanBridges.Counting.choose (n : ℤ) (2 : ℤ) : ℤ) + (n : ℤ) = (LeanBridges.Counting.choose ((n : ℤ) + 1) (2 : ℤ) : ℤ) := by parley_subst_at c1 s2
    exact row1
  -- 4. calculation
  have s4 : (n : ℤ) + (LeanBridges.Counting.choose (n : ℤ) (2 : ℤ) : ℤ) = (LeanBridges.Counting.choose ((n : ℤ) + 1) (2 : ℤ) : ℤ) := by
    calc (n : ℤ) + (LeanBridges.Counting.choose (n : ℤ) (2 : ℤ) : ℤ) = (LeanBridges.Counting.choose (n : ℤ) (2 : ℤ) : ℤ) + (n : ℤ) := by parley_ring
      _ = (LeanBridges.Counting.choose ((n : ℤ) + 1) (2 : ℤ) : ℤ) := by parley_side
  all_goals parley_side

end Parley.Proofs.Setmm.ChooseTwoPairs.ChooseTwoPairs
