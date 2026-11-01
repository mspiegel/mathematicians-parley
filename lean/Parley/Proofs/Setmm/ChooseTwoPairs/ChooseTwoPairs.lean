module

public import Parley.Items.Stdlib.Counting
public import Parley.Library
public import Parley.Proofs.Setmm.ChooseTwoPairs.ChooseOne

/-! Written from proofs/setmm/choose-two-pairs.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.ChooseTwoPairs.ChooseTwoPairs

theorem choose_two_pairs (n : ℕ) :
    (n : ℤ) + (Parley.Library.choose (n : ℤ) (2 : ℤ) : ℤ) = (Parley.Library.choose ((n : ℤ) + 1) (2 : ℤ) : ℤ) := by
  -- 1. thm:pascal k := 2
  have s1 : (Parley.Library.choose (n : ℤ) (2 : ℤ) : ℤ) + (Parley.Library.choose (n : ℤ) (2 - 1 : ℤ) : ℤ) = (Parley.Library.choose ((n : ℤ) + 1) (2 : ℤ) : ℤ) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.thm_pascal (n := n) (k := (2 : ℤ))) | (have h := (Parley.Items.Stdlib.Counting.thm_pascal (n := n) (k := (2 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | exact_mod_cast (Parley.Items.Stdlib.Counting.thm_pascal (n := n) (k := (2 : ℤ))) | exact_mod_cast ((Parley.Items.Stdlib.Counting.thm_pascal (n := n) (k := (2 : ℤ)))).symm
  -- 2. substitute 2 − 1 = 1 (arithmetic) into line 1
  have s2 : (Parley.Library.choose (n : ℤ) (2 : ℤ) : ℤ) + (Parley.Library.choose (n : ℤ) (1 : ℤ) : ℤ) = (Parley.Library.choose ((n : ℤ) + 1) (2 : ℤ) : ℤ) := by parley_subst_at (show (2 - 1 : ℤ) = 1 by parley_side) s1
  -- 3. substitute
  have s3 : (Parley.Library.choose (n : ℤ) (2 : ℤ) : ℤ) + (n : ℤ) = (Parley.Library.choose ((n : ℤ) + 1) (2 : ℤ) : ℤ) := by
    have c1 : (Parley.Library.choose (n : ℤ) (1 : ℤ) : ℤ) = (n : ℤ) := by first | linear_combination (norm := parley_norm) (Parley.Proofs.Setmm.ChooseTwoPairs.ChooseOne.choose_one (n := n)) | (have h := (Parley.Proofs.Setmm.ChooseTwoPairs.ChooseOne.choose_one (n := n)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | exact_mod_cast (Parley.Proofs.Setmm.ChooseTwoPairs.ChooseOne.choose_one (n := n)) | exact_mod_cast ((Parley.Proofs.Setmm.ChooseTwoPairs.ChooseOne.choose_one (n := n))).symm
    have row1 : (Parley.Library.choose (n : ℤ) (2 : ℤ) : ℤ) + (n : ℤ) = (Parley.Library.choose ((n : ℤ) + 1) (2 : ℤ) : ℤ) := by parley_subst_at c1 s2
    exact row1
  -- 4. calculation
  have s4 : (n : ℤ) + (Parley.Library.choose (n : ℤ) (2 : ℤ) : ℤ) = (Parley.Library.choose ((n : ℤ) + 1) (2 : ℤ) : ℤ) := by
    calc (n : ℤ) + (Parley.Library.choose (n : ℤ) (2 : ℤ) : ℤ) = (Parley.Library.choose (n : ℤ) (2 : ℤ) : ℤ) + (n : ℤ) := by parley_ring
      _ = (Parley.Library.choose ((n : ℤ) + 1) (2 : ℤ) : ℤ) := by parley_side
  all_goals parley_side

end Parley.Proofs.Setmm.ChooseTwoPairs.ChooseTwoPairs
