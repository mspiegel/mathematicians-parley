module

public import Parley.Items.Stdlib.Counting
public import Parley.Library

/-! Written from proofs/setmm/binomial-basics.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.BinomialBasics.FactorialNonzero

theorem factorial_nonzero (N : ℕ) :
    (Parley.Library.factorial (N : ℤ) : ℤ) ≠ 0 := by
  -- 1. mun:factorial-nat n := N
  have s1 : 0 < (Parley.Library.factorial (N : ℤ) : ℤ) := by first | exact (Parley.Items.Stdlib.Counting.mun_factorial_nat (n := N)) | exact ((Parley.Items.Stdlib.Counting.mun_factorial_nat (n := N))).symm | simpa using (Parley.Items.Stdlib.Counting.mun_factorial_nat (n := N)) | exact_mod_cast (Parley.Items.Stdlib.Counting.mun_factorial_nat (n := N))
  -- 2. inequalities, from 1
  have s2 : (Parley.Library.factorial (N : ℤ) : ℤ) ≠ 0 := by parley_side
  all_goals parley_side

end Parley.Proofs.Setmm.BinomialBasics.FactorialNonzero
