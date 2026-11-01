module

public import Parley.Items.Stdlib.Divisibility
public import Parley.Library

/-! Written from tests/notations/divisibility.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Divisibility.MinusOneFourModFive

theorem minus_one_four_mod_five :
    (-1 : ℤ) ≡ (4 : ℤ) [ZMOD (5 : ℤ)] := by
  -- 1. arithmetic
  have s1 : (-1 - 4 : ℤ) = 5 * -1 := by parley_arith
  -- 2. def:divides d := 5, n := −1 − 4, from 1
  have s2 : (5 : ℤ) ∣ (-1 - 4 : ℤ) := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (5 : ℤ)) (n := (-1 - 4 : ℤ)))).mpr ⟨(-1 : ℤ), by parley_side⟩
  -- 3. def:congruent-mod n := 5, a := −1, b := 4, from 2
  have s3 : (-1 : ℤ) ≡ (4 : ℤ) [ZMOD (5 : ℤ)] := ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := (5 : ℤ)) (a := (-1 : ℤ)) (b := (4 : ℤ)))).mpr (by parley_side)
  all_goals parley_side

end Parley.Tests.Notations.Divisibility.MinusOneFourModFive
