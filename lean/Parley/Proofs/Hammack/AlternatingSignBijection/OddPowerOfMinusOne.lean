module

public import Parley.Items.Stdlib.Numbers
public import Parley.Library
public import Parley.Proofs.Hammack.AlternatingSignBijection.EvenPowerOfMinusOne

/-! Written from proofs/hammack/alternating-sign-bijection.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.AlternatingSignBijection.OddPowerOfMinusOne

theorem odd_power_of_minus_one (k : ℕ) :
    ((-1) ^ (2 * k + 1) : ℤ) = -1 := by
  -- 1. thm:even-power-of-minus-one
  have s1 : ((-1) ^ (2 * k) : ℤ) = 1 := by linear_combination (Parley.Proofs.Hammack.AlternatingSignBijection.EvenPowerOfMinusOne.even_power_of_minus_one (k := k))
  -- 2. calculation
  have s2 : ((-1) ^ (2 * k + 1) : ℤ) = -1 := by
    calc ((-1) ^ (2 * k + 1) : ℤ) = (-1) ^ (2 * k) * -1 := by linear_combination (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (-1 : ℤ)) (m := 2 * k))
      _ = 1 * -1 := by parley_subst s1
      _ = -1 := by norm_num
  all_goals parley_side

end Parley.Proofs.Hammack.AlternatingSignBijection.OddPowerOfMinusOne
