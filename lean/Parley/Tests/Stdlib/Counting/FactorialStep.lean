module

public import Parley.Items.Stdlib.Counting
public import Parley.Library

/-! Written from tests/stdlib/counting.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Counting.FactorialStep

theorem factorial_step (n : ℕ) :
    (Parley.Library.factorial ((n : ℤ) + 1) : ℤ) = (Parley.Library.factorial (n : ℤ) : ℤ) * ((n : ℤ) + 1) := by
  -- 1. def:factorial
  have s1 : (Parley.Library.factorial ((n : ℤ) + 1) : ℤ) = (Parley.Library.factorial (n : ℤ) : ℤ) * ((n : ℤ) + 1) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.def_factorial_3 (n := n)) | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := n)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | exact_mod_cast (Parley.Items.Stdlib.Counting.def_factorial_3 (n := n)) | exact_mod_cast ((Parley.Items.Stdlib.Counting.def_factorial_3 (n := n))).symm | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := n)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := n)); qify; linear_combination (norm := parley_norm) h)
  all_goals parley_side

end Parley.Tests.Stdlib.Counting.FactorialStep
