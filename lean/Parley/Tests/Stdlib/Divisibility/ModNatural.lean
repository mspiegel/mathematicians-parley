module

public import Tactics
public import Mathlib.Data.Int.Notation
public import Parley.Items.Stdlib.Divisibility

/-! Written from tests/stdlib/divisibility.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Divisibility.ModNatural

theorem mod_natural (a : ℤ) (b : ℤ) (hH2 : 0 < b) :
    0 ≤ a % b := by
  -- 1. mun:divisibility-mod-natural
  have s1 : 0 ≤ a % b := by first | exact (Parley.Items.Stdlib.Divisibility.mun_mod_natural (a := a) (b := b) (by parley_side)) | exact ((Parley.Items.Stdlib.Divisibility.mun_mod_natural (a := a) (b := b) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_mod_natural (a := a) (b := b) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_mod_natural (a := a) (b := b) (by parley_side)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_natural (a := a) (b := b) (by parley_side)); parley_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Divisibility.ModNatural
