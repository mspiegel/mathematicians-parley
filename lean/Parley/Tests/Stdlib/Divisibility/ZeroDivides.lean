module

public import Tactics
public import Parley.Items.Stdlib.Divisibility

/-! Written from tests/stdlib/divisibility.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Divisibility.ZeroDivides

theorem zero_divides (n : ℤ) :
    ((0 : ℤ) ∣ n ↔ n = 0) := by
  -- 1. mun:divisibility-zero-divides
  have s1 : (0 : ℤ) ∣ n ↔ n = 0 := by first | exact (Parley.Items.Stdlib.Divisibility.mun_zero_divides (n := n)) | exact ((Parley.Items.Stdlib.Divisibility.mun_zero_divides (n := n))).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_zero_divides (n := n)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_zero_divides (n := n)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_zero_divides (n := n)); parley_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Divisibility.ZeroDivides
