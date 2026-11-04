module

public import Tactics
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/stdlib/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Numbers.NatPlusNat0

theorem nat_plus_nat0 (p : ℕ) (hH1 : 0 < p) (q : ℕ) :
    0 < (p : ℤ) + (q : ℤ) := by
  -- 1. mun:numbers-nat-plus-nat0 a := p, b := q
  have s1 : 0 < (p : ℤ) + (q : ℤ) := by first | exact (Parley.Items.Stdlib.Numbers.mun_nat_plus_nat0 (a := p) (by parley_side) (b := q)) | exact ((Parley.Items.Stdlib.Numbers.mun_nat_plus_nat0 (a := p) (by parley_side) (b := q))).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_nat_plus_nat0 (a := p) (by parley_side) (b := q)) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_nat_plus_nat0 (a := p) (by parley_side) (b := q)) | (have h := (Parley.Items.Stdlib.Numbers.mun_nat_plus_nat0 (a := p) (by parley_side) (b := q)); parley_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Numbers.NatPlusNat0
