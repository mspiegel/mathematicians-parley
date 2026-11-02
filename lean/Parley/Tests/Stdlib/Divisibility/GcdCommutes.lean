module

public import Parley.Items.Stdlib.Divisibility
public import Parley.Library

/-! Written from tests/stdlib/divisibility.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Divisibility.GcdCommutes

theorem gcd_commutes (a : ℤ) (b : ℤ) :
    (Int.gcd a b : ℤ) = (Int.gcd b a : ℤ) := by
  -- 1. mun:divisibility-gcd-commutes
  have s1 : (Int.gcd a b : ℤ) = (Int.gcd b a : ℤ) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Divisibility.mun_gcd_commutes (a := a) (b := b)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_gcd_commutes (a := a) (b := b)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_gcd_commutes (a := a) (b := b)) | exact_mod_cast ((Parley.Items.Stdlib.Divisibility.mun_gcd_commutes (a := a) (b := b))).symm
  all_goals parley_side

end Parley.Tests.Stdlib.Divisibility.GcdCommutes
