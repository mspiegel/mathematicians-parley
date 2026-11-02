module

public import LeanBridges
public import Parley.Items.Stdlib.Divisibility

/-! Written from tests/notations/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Numbers.MinusOneModFive

theorem minus_one_mod_five :
    (-1 : ℤ) % (5 : ℤ) = 4 := by
  -- 1. arithmetic
  have s1 : (-1 * 5 + 4 : ℤ) = -1 := by parley_arith
  -- 2. exhibit, from 1
  have s2 : ∃ q : ℤ, q * 5 + 4 = -1 := ⟨(-1 : ℤ), by parley_side⟩
  -- 3. mun:mod-remainder a := −1, m := 5, r := 4, from 2
  have r57_1 : (4 : ℤ) < 5 := by parley_arith
  have s3 : (-1 : ℤ) % (5 : ℤ) = 4 := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.mun_mod_remainder (a := (-1 : ℤ)) (m := 5) (by parley_side) (r := 4) (by parley_side))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Divisibility.mun_mod_remainder (a := (-1 : ℤ)) (m := 5) (by parley_side) (r := 4) (by parley_side))).mpr (by parley_side); parley_side)
  all_goals parley_side

end Parley.Tests.Notations.Numbers.MinusOneModFive
