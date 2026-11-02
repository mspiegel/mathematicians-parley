module

public import LeanBridges
public import Parley.Items.Stdlib.Divisibility

/-! Written from tests/stdlib/divisibility.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Divisibility.GcdMod

theorem gcd_mod (a : ℤ) (b : ℕ) (hH2 : 0 < b) :
    (Int.gcd (a % (b : ℤ)) (b : ℤ) : ℤ) = (Int.gcd a (b : ℤ) : ℤ) := by
  -- 1. thm:divisibility-gcd-mod
  have s1 : (Int.gcd (a % (b : ℤ)) (b : ℤ) : ℤ) = (Int.gcd a (b : ℤ) : ℤ) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Divisibility.thm_gcd_mod (a := a) (b := b) (by parley_side)) | (have h := (Parley.Items.Stdlib.Divisibility.thm_gcd_mod (a := a) (b := b) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.thm_gcd_mod (a := a) (b := b) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Divisibility.thm_gcd_mod (a := a) (b := b) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Divisibility.thm_gcd_mod (a := a) (b := b) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.thm_gcd_mod (a := a) (b := b) (by parley_side)); qify; linear_combination (norm := parley_norm) h)
  all_goals parley_side

end Parley.Tests.Stdlib.Divisibility.GcdMod
