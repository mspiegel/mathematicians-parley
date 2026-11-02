module

public import Parley.Items.Stdlib.Counting
public import Parley.Library

/-! Written from tests/stdlib/counting.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Counting.BinomialCoefficient

theorem binomial_coefficient (n : ℕ) (k : ℤ) (k : ℤ) (hH3 : k ∈ Finset.Icc (0 : ℤ) (n : ℤ)) :
    (Parley.Library.choose (n : ℤ) k : ℚ) = (Parley.Library.factorial (n : ℤ) : ℚ) / ((Parley.Library.factorial ((n : ℤ) - k) : ℚ) * (Parley.Library.factorial k : ℚ)) := by
  -- 1. def:C, from H3
  have s1 : (Parley.Library.choose (n : ℤ) k : ℚ) = (Parley.Library.factorial (n : ℤ) : ℚ) / ((Parley.Library.factorial ((n : ℤ) - k) : ℚ) * (Parley.Library.factorial k : ℚ)) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.def_C_2 (n := n) (k := k)) (by parley_side) | (have h := (Parley.Items.Stdlib.Counting.def_C_2 (n := n) (k := k)) (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | exact_mod_cast (Parley.Items.Stdlib.Counting.def_C_2 (n := n) (k := k)) (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Counting.def_C_2 (n := n) (k := k)) (by parley_side)).symm
  all_goals parley_side

end Parley.Tests.Stdlib.Counting.BinomialCoefficient
