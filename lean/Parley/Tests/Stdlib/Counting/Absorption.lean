module

public import Parley.Items.Stdlib.Counting
public import Parley.Library

/-! Written from tests/stdlib/counting.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Counting.Absorption

theorem absorption (n : ℕ) (k : ℤ) (hH2 : k ∈ Finset.Icc (0 : ℤ) (n : ℤ)) :
    (Parley.Library.choose ((n : ℤ) + 1) (k + 1) : ℚ) = (Parley.Library.choose (n : ℤ) k : ℚ) * (((n : ℚ) + 1) / ((k : ℚ) + 1)) := by
  -- 1. thm:counting-absorption, from H2
  have s1 : (Parley.Library.choose ((n : ℤ) + 1) (k + 1) : ℚ) = (Parley.Library.choose (n : ℤ) k : ℚ) * (((n : ℚ) + 1) / ((k : ℚ) + 1)) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.thm_absorption (n := n) (k := k) (by parley_side)) | (have h := (Parley.Items.Stdlib.Counting.thm_absorption (n := n) (k := k) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | exact_mod_cast (Parley.Items.Stdlib.Counting.thm_absorption (n := n) (k := k) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Counting.thm_absorption (n := n) (k := k) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Counting.thm_absorption (n := n) (k := k) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.thm_absorption (n := n) (k := k) (by parley_side)); qify; linear_combination (norm := parley_norm) h)
  all_goals parley_side

end Parley.Tests.Stdlib.Counting.Absorption
