module

public import Parley.Items.Stdlib.Numbers
public import Parley.Library

/-! Written from proofs/hammack/mersenne-prime-exponent.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.MersennePrimeExponent.TwoPowerBound

theorem two_power_bound (d : ℕ) (H1 : 0 < d) :
    2 ^ d ≥ (d : ℤ) + 1 := by
  -- 1. induction on m starting at 1
  have s1 : ∀ m : ℕ, 0 < m → 2 ^ m ≥ (m : ℤ) + 1 := by
    intro m h_m
    have h1_m : 1 ≤ m := h_m
    induction m, h1_m using Nat.le_induction with
    | base =>
      -- 1.1. arithmetic
      have s1_1 : (2 ^ 1 : ℤ) ≥ 1 + 1 := by parley_arith
      all_goals parley_side
    | succ m K IH =>
      -- 1.2. mun:exponent-step a := 2
      have s1_2 : (2 ^ (m + 1) : ℤ) = 2 ^ m * 2 := by linear_combination (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := m))
      -- 1.3. inequalities
      have s1_3 : 2 ^ m * 2 ≥ ((m : ℤ) + 1) * 2 := by parley_side
      -- 1.4. inequalities, from K
      have s1_4 : ((m : ℤ) + 1) * 2 ≥ (m : ℤ) + 1 + 1 := by parley_side
      -- 1.5. transitivity, from 1.2, 1.3, 1.4
      have s1_5 : 2 ^ (m + 1) ≥ (m : ℤ) + 1 + 1 := by parley_side
      all_goals parley_side
  -- 2. instantiate m := d in line 1
  have s2 : 2 ^ d ≥ (d : ℤ) + 1 := by linarith [(s1 d (by parley_side))]
  all_goals parley_side

end Parley.Proofs.Hammack.MersennePrimeExponent.TwoPowerBound
