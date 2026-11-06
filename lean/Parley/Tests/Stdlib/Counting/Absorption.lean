module

public import Counting
public import FactorialTactics
public import PowerTactics
public import Tactics
public import Parley.Items.Stdlib.Counting

/-! Written from tests/stdlib/counting.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Counting.Absorption

theorem absorption (n : ℤ) (hH1 : 0 ≤ n) (k : ℤ) (hH2 : k ∈ Finset.Icc (0 : ℤ) n) :
    (LeanBridges.Counting.choose (n + 1) (k + 1) : ℚ) = (LeanBridges.Counting.choose n k : ℚ) * (((n : ℚ) + 1) / ((k : ℚ) + 1)) := by
  -- 1. thm:counting-absorption, from H2
  have s1 : (LeanBridges.Counting.choose (n + 1) (k + 1) : ℚ) = (LeanBridges.Counting.choose n k : ℚ) * (((n : ℚ) + 1) / ((k : ℚ) + 1)) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.thm_absorption (n := n) (by parley_side) (k := k) hH2) | (have h := (Parley.Items.Stdlib.Counting.thm_absorption (n := n) (by parley_side) (k := k) hH2); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.thm_absorption (n := n) (by parley_side) (k := k) hH2); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Counting.thm_absorption (n := n) (by parley_side) (k := k) hH2) | exact_mod_cast ((Parley.Items.Stdlib.Counting.thm_absorption (n := n) (by parley_side) (k := k) hH2)).symm | (have h := (Parley.Items.Stdlib.Counting.thm_absorption (n := n) (by parley_side) (k := k) hH2); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.thm_absorption (n := n) (by parley_side) (k := k) hH2); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.thm_absorption (n := n) (by parley_side) (k := k) hH2); parley_int_power h) | (have h := (Parley.Items.Stdlib.Counting.thm_absorption (n := n) (by parley_side) (k := k) hH2); parley_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Counting.Absorption
