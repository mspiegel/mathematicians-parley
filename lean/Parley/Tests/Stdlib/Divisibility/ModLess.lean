module

public import LeanBridges
public import Parley.Items.Stdlib.Divisibility

/-! Written from tests/stdlib/divisibility.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Divisibility.ModLess

theorem mod_less (a : ℤ) (b : ℕ) (hH2 : 0 < b) :
    a % (b : ℤ) < (b : ℤ) := by
  -- 1. mun:divisibility-mod-less
  have s1 : a % (b : ℤ) < (b : ℤ) := by first | linarith [(Parley.Items.Stdlib.Divisibility.mun_mod_less (a := a) (b := b) (by parley_side))] | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_less (a := a) (b := b) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_mod_less (a := a) (b := b) (by parley_side)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_less (a := a) (b := b) (by parley_side)); parley_side)
  all_goals parley_side

end Parley.Tests.Stdlib.Divisibility.ModLess
