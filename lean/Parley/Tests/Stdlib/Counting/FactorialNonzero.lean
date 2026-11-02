module

public import Parley.Items.Stdlib.Counting
public import Parley.Library

/-! Written from tests/stdlib/counting.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Counting.FactorialNonzero

theorem factorial_nonzero (n : ℕ) :
    (Parley.Library.factorial (n : ℤ) : ℤ) ≠ 0 := by
  -- 1. mun:counting-factorial-nonzero
  have s1 : (Parley.Library.factorial (n : ℤ) : ℤ) ≠ 0 := by first | exact (Parley.Items.Stdlib.Counting.mun_factorial_nonzero (n := n)) | exact ((Parley.Items.Stdlib.Counting.mun_factorial_nonzero (n := n))).symm | simpa using (Parley.Items.Stdlib.Counting.mun_factorial_nonzero (n := n)) | exact_mod_cast (Parley.Items.Stdlib.Counting.mun_factorial_nonzero (n := n))
  all_goals parley_side

end Parley.Tests.Stdlib.Counting.FactorialNonzero
