module

public import Tactics
public import Parley.Items.Stdlib.Divisibility

/-! Written from tests/stdlib/divisibility.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Divisibility.GcdInteger

theorem gcd_integer (a : ℤ) (b : ℤ) :
    (Int.gcd a b : ℤ) ∣ b := by
  -- 1. mun:divisibility-gcd-integer
  have s1 : (Int.gcd a b : ℤ) ∣ b := by first | exact (Parley.Items.Stdlib.Divisibility.mun_gcd_integer_3 (a := a) (b := b)) | exact ((Parley.Items.Stdlib.Divisibility.mun_gcd_integer_3 (a := a) (b := b))).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_gcd_integer_3 (a := a) (b := b)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_gcd_integer_3 (a := a) (b := b)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_gcd_integer_3 (a := a) (b := b)); parley_side)
  all_goals parley_side

end Parley.Tests.Stdlib.Divisibility.GcdInteger
