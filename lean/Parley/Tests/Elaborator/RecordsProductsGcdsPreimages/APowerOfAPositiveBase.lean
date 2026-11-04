module

public import ArithTactics
public import Tactics
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/elaborator/records-products-gcds-preimages.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RecordsProductsGcdsPreimages.APowerOfAPositiveBase

theorem a_power_of_a_positive_base (n : ℕ) (hH1 : 0 < n) :
    (2 ^ n : ℤ) > 0 := by
  -- 1. mun:power-positive a := 2, m := n
  have r58_1 : (2 : ℤ) > 0 := by parley_arith
  have s1 : (2 ^ n : ℤ) > 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_power_positive (a := (2 : ℚ)) (m := (n : ℤ)) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_power_positive (a := (2 : ℚ)) (m := (n : ℤ)) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_power_positive (a := (2 : ℚ)) (m := (n : ℤ)) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_power_positive (a := (2 : ℚ)) (m := (n : ℤ)) (by parley_side)); parley_side)
  all_goals exact s1

end Parley.Tests.Elaborator.RecordsProductsGcdsPreimages.APowerOfAPositiveBase
