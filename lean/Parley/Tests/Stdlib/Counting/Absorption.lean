module

public import Counting
public import PowerTactics
public import Tactics
public import Parley.Items.Stdlib.Counting

/-! Written from tests/stdlib/counting.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Counting.Absorption

theorem absorption (n : ℕ) (k : ℤ) (hH2 : k ∈ Finset.Icc (0 : ℤ) (n : ℤ)) :
    (LeanBridges.Counting.choose ((n : ℤ) + 1) (k + 1) : ℚ) = (LeanBridges.Counting.choose (n : ℤ) k : ℚ) * (((n : ℚ) + 1) / ((k : ℚ) + 1)) := by
  -- 1. thm:counting-absorption, from H2
  have s1 : (LeanBridges.Counting.choose ((n : ℤ) + 1) (k + 1) : ℚ) = (LeanBridges.Counting.choose (n : ℤ) k : ℚ) * (((n : ℚ) + 1) / ((k : ℚ) + 1)) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.thm_absorption (n := n) (k := k) (by parley_side)) | (have h := (Parley.Items.Stdlib.Counting.thm_absorption (n := n) (k := k) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.thm_absorption (n := n) (k := k) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Counting.thm_absorption (n := n) (k := k) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Counting.thm_absorption (n := n) (k := k) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Counting.thm_absorption (n := n) (k := k) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.thm_absorption (n := n) (k := k) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.thm_absorption (n := n) (k := k) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Counting.thm_absorption (n := n) (k := k) (by parley_side)); parley_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Counting.Absorption
