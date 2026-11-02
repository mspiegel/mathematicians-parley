module

public import LeanBridges
public import Parley.Items.Stdlib.Counting

/-! Written from tests/stdlib/counting.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Counting.BinomialCoefficient

theorem binomial_coefficient (n : ℕ) (k : ℤ) (k : ℤ) (hH3 : k ∈ Finset.Icc (0 : ℤ) (n : ℤ)) :
    (LeanBridges.Counting.choose (n : ℤ) k : ℚ) = (LeanBridges.Counting.factorial (n : ℤ) : ℚ) / ((LeanBridges.Counting.factorial ((n : ℤ) - k) : ℚ) * (LeanBridges.Counting.factorial k : ℚ)) := by
  -- 1. def:C, from H3
  have s1 : (LeanBridges.Counting.choose (n : ℤ) k : ℚ) = (LeanBridges.Counting.factorial (n : ℤ) : ℚ) / ((LeanBridges.Counting.factorial ((n : ℤ) - k) : ℚ) * (LeanBridges.Counting.factorial k : ℚ)) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.def_C_2 (n := n) (k := k)) (by parley_side) | (have h := (Parley.Items.Stdlib.Counting.def_C_2 (n := n) (k := k)) (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | exact_mod_cast (Parley.Items.Stdlib.Counting.def_C_2 (n := n) (k := k)) (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Counting.def_C_2 (n := n) (k := k)) (by parley_side)).symm | (have h := (Parley.Items.Stdlib.Counting.def_C_2 (n := n) (k := k)) (by parley_side); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_C_2 (n := n) (k := k)) (by parley_side); qify; linear_combination (norm := parley_norm) h)
  all_goals parley_side

end Parley.Tests.Stdlib.Counting.BinomialCoefficient
