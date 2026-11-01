module

public import Parley.Items.Stdlib.Numbers
public import Parley.Library

/-! Written from proofs/setmm/minus-one-even-power.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.MinusOneEvenPower.MinusOneEvenPowerNatural

theorem minus_one_even_power_natural (n : ℕ) :
    ((-1) ^ (2 * n) : ℤ) = 1 := by
  -- 1. induction on k starting at 0
  have s1 : ∀ k : ℕ, ((-1) ^ (2 * k) : ℤ) = 1 := by
    intro k
    induction k with
    | zero =>
      -- 1.1. arithmetic
      have s1_1 : ((-1) ^ (2 * 0) : ℤ) = 1 := by parley_arith
      all_goals parley_side
    | succ k IH =>
      -- 1.2. algebra
      have s1_2 : 2 * ((k : ℤ) + 1) = 2 * (k : ℤ) + 1 + 1 := by ring
      -- 1.3. calculation
      have s1_3 : ((-1) ^ (2 * k + 1) : ℤ) = -1 := by
        calc ((-1) ^ (2 * k + 1) : ℤ) = (-1) ^ (2 * k) * -1 := by linear_combination (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (-1 : ℤ)) (m := 2 * k))
          _ = 1 * -1 := by parley_subst IH
          _ = -1 := by norm_num
      -- 1.4. calculation
      have s1_4 : ((-1) ^ (2 * (k + 1)) : ℤ) = 1 := by
        calc ((-1) ^ (2 * (k + 1)) : ℤ) = (-1) ^ (2 * k + 1 + 1) := by parley_subst s1_2
          _ = (-1) ^ (2 * k + 1) * -1 := by linear_combination (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (-1 : ℤ)) (m := 2 * k + 1))
          _ = -1 * -1 := by parley_subst s1_3
          _ = 1 := by norm_num
      all_goals parley_side
  -- 2. instantiate k := n in line 1
  have s2 : ((-1) ^ (2 * n) : ℤ) = 1 := by linear_combination (s1 n)
  all_goals parley_side

end Parley.Proofs.Setmm.MinusOneEvenPower.MinusOneEvenPowerNatural
