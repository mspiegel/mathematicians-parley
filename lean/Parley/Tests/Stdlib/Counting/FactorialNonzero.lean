module

public import Counting
public import Tactics
public import Parley.Items.Stdlib.Counting

/-! Written from tests/stdlib/counting.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Counting.FactorialNonzero

theorem factorial_nonzero (n : ℕ) :
    (LeanBridges.Counting.factorial (n : ℤ) : ℤ) ≠ 0 := by
  -- 1. mun:counting-factorial-nonzero
  have s1 : (LeanBridges.Counting.factorial (n : ℤ) : ℤ) ≠ 0 := by first | exact (Parley.Items.Stdlib.Counting.mun_factorial_nonzero (n := n)) | exact ((Parley.Items.Stdlib.Counting.mun_factorial_nonzero (n := n))).symm | simpa using (Parley.Items.Stdlib.Counting.mun_factorial_nonzero (n := n)) | exact_mod_cast (Parley.Items.Stdlib.Counting.mun_factorial_nonzero (n := n)) | (have h := (Parley.Items.Stdlib.Counting.mun_factorial_nonzero (n := n)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Counting.mun_factorial_nonzero (n := n)); parley_side)
  all_goals parley_side

end Parley.Tests.Stdlib.Counting.FactorialNonzero
