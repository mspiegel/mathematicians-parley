module

public import Parley.Items.Stdlib.Numbers
public import Parley.Library

/-! Written from proofs/hammack/nine-powers-and-three-powers.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.NinePowersAndThreePowers.NinePowerFromZero

theorem nine_power_from_zero (n : ℕ) :
    (9 ^ n : ℤ) = 3 ^ n * 3 ^ n := by
  -- 1. induction on k starting at 0
  have s1 : ∀ k : ℕ, (9 ^ k : ℤ) = 3 ^ k * 3 ^ k := by
    intro k
    induction k with
    | zero =>
      -- 1.1. arithmetic
      have s1_1 : (9 ^ 0 : ℤ) = 3 ^ 0 * 3 ^ 0 := by parley_arith
      all_goals parley_side
    | succ k IH =>
      -- 1.2. mun:exponent-step a := 9, m := k
      have s1_2 : (9 ^ (k + 1) : ℤ) = 9 ^ k * 9 := by linear_combination (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (9 : ℤ)) (m := k))
      -- 1.3. mun:exponent-step a := 3, m := k
      have s1_3 : (3 ^ (k + 1) : ℤ) = 3 ^ k * 3 := by linear_combination (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (3 : ℤ)) (m := k))
      -- 1.4. algebra, from IH, 1.2, 1.3
      have s1_4 : (9 ^ (k + 1) : ℤ) = 3 ^ (k + 1) * 3 ^ (k + 1) := by linear_combination (9) * IH + s1_2 + (-3 ^ (k + 1) - 3 * 3 ^ k) * s1_3
      all_goals parley_side
  -- 2. instantiate k := n in line 1
  have s2 : (9 ^ n : ℤ) = 3 ^ n * 3 ^ n := by linear_combination (s1 n)
  all_goals parley_side

end Parley.Proofs.Hammack.NinePowersAndThreePowers.NinePowerFromZero
