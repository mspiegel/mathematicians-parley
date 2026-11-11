module

public import AlgebraTactics
public import ArithTactics
public import InstanceTactics
public import NormTactics
public import OrderTactics
public import PowerTactics
public import Tactics
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Rat.Init
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers
public import Parley.Proofs.Hammack.NinePowersAndThreePowers.NinePowerFromZero
public import Parley.Proofs.Hammack.NinePowersAndThreePowers.PositivePowerIsReal

/-! Written from proofs/hammack/nine-powers-and-three-powers.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.NinePowersAndThreePowers.NinePowerIsThreePower

theorem nine_power_is_three_power (m : ℤ) :
    (9 ^ m : ℚ) = 3 ^ (2 * m) := by
  -- 1. mun:nonneg-or-neg x := m
  have s1 : m ≥ 0 ∨ m < 0 := by exact (Parley.Items.Stdlib.Numbers.mun_nonneg_or_neg (x := m))
  -- 2. mun:exponent-sum-integer a := 3, n := m
  have r109_1 : (3 : ℤ) ≠ 0 := by parley_arith
  have s2 : (3 ^ (m + m) : ℚ) = 3 ^ m * 3 ^ m := by exact (Parley.Items.Stdlib.Numbers.mun_exponent_sum_integer (a := (3 : ℚ)) (by parley_side) (m := m) (n := m))
  -- 3. substitute
  have s3 : (3 ^ (2 * m) : ℚ) = 3 ^ m * 3 ^ m := by
    have c1 : m + m = 2 * m := by parley_ring
    have row1 : (3 ^ (2 * m) : ℚ) = 3 ^ m * 3 ^ m := by (have h := Eq.subst (motive := (fun t : ℤ => (3 ^ t : ℚ) = 3 ^ m * 3 ^ m)) c1 s2; push_cast at h ⊢; all_goals exact_mod_cast h)
    exact row1
  -- 4. cases, from 1
  have s4 : (9 ^ m : ℚ) = 3 ^ m * 3 ^ m := by
    rcases s1 with hC1 | hC2
    · skip
      -- 4.1. mun:nat0-as-int
      have r124_1 : 0 ≤ m := by exact hC1
      have s4_1 : 0 ≤ m := by
        have hI : 0 ≤ m := by parley_instance (((Parley.Items.Stdlib.Numbers.mun_nat0_as_int (n := m))).mpr ⟨by parley_side, r124_1⟩)
        exact hI
      -- 4.2. thm:nine-power-from-zero n := m, from 4.1
      (have h := (Parley.Proofs.Hammack.NinePowersAndThreePowers.NinePowerFromZero.nine_power_from_zero (n := m) s4_1); simp only [parley_zpow_toNat (n := m) (h := s4_1)] at h ⊢; exact_mod_cast h)
    · skip
      -- 4.3. inequalities
      have s4_3 : -m > 0 := by parley_order
      -- 4.4. mun:nat0-as-int
      have r139_1 : -m ≥ 0 := by parley_side
      have s4_4 : 0 ≤ -m := by
        have hI : 0 ≤ -m := by parley_instance (((Parley.Items.Stdlib.Numbers.mun_nat0_as_int (n := -m))).mpr ⟨by parley_side, r139_1⟩)
        exact hI
      -- 4.5. thm:nine-power-from-zero n := −m, from 4.4
      have s4_5 : (9 ^ (-m) : ℚ) = 3 ^ (-m) * 3 ^ (-m) := by (have h := (Parley.Proofs.Hammack.NinePowersAndThreePowers.NinePowerFromZero.nine_power_from_zero (n := -m) s4_4); simp only [parley_zpow_toNat (n := -m) (h := s4_4)] at h ⊢; exact_mod_cast h)
      -- 4.6. thm:positive-power-is-real a := 9
      have r146_1 : (9 : ℤ) > 0 := by parley_arith
      -- 4.7. thm:positive-power-is-real a := 3
      have r150_1 : (3 : ℤ) > 0 := by parley_arith
      -- 4.8. mun:power-positive a := 9
      have r154_1 : (0 : ℤ) < 9 := by parley_arith
      have s4_8 : (9 ^ m : ℚ) > 0 := by exact (Parley.Items.Stdlib.Numbers.mun_power_positive (a := (9 : ℚ)) (m := m) (by parley_side))
      -- 4.9. mun:power-positive a := 3
      have r158_1 : (0 : ℤ) < 3 := by parley_arith
      have s4_9 : (3 ^ m : ℚ) > 0 := by exact (Parley.Items.Stdlib.Numbers.mun_power_positive (a := (3 : ℚ)) (m := m) (by parley_side))
      -- 4.10. substitute
      have r162_1 : (9 : ℤ) ≠ 0 := by parley_arith
      have s4_10 : (1 / 9 ^ m : ℚ) = 3 ^ (-m) * 3 ^ (-m) := by
        have c1 : (9 ^ (-m) : ℚ) = 1 / 9 ^ m := by exact (Parley.Items.Stdlib.Numbers.mun_exponent_negative (a := (9 : ℚ)) (by parley_side) (m := m))
        have row1 : (1 / 9 ^ m : ℚ) = 3 ^ (-m) * 3 ^ (-m) := by (have h := Eq.subst (motive := (fun t : ℚ => t = 3 ^ (-m) * 3 ^ (-m))) c1 s4_5; push_cast at h ⊢; all_goals exact_mod_cast h)
        exact row1
      -- 4.11. substitute
      have r168_1 : (3 : ℤ) ≠ 0 := by parley_arith
      have s4_11 : (1 / 9 ^ m : ℚ) = 1 / 3 ^ m * (1 / 3 ^ m) := by
        have c1 : (3 ^ (-m) : ℚ) = 1 / 3 ^ m := by exact (Parley.Items.Stdlib.Numbers.mun_exponent_negative (a := (3 : ℚ)) (by parley_side) (m := m))
        have row1 : (1 / 9 ^ m : ℚ) = 1 / 3 ^ m * (1 / 3 ^ m) := by (have h := Eq.subst (motive := (fun t : ℚ => 1 / 9 ^ m = t * t)) c1 s4_10; push_cast at h ⊢; all_goals exact_mod_cast h)
        exact row1
      -- 4.12. inequalities
      have s4_12 : (9 ^ m : ℚ) ≠ 0 := by parley_side
      -- 4.13. inequalities
      have s4_13 : (3 ^ m : ℚ) ≠ 0 := by parley_side
      -- 4.14. algebra, from 4.6, 4.7, 4.11
      have r186_1 : (9 ^ m : ℚ) ≠ 0 := by exact s4_12
      have r186_2 : (3 ^ m : ℚ) ≠ 0 := by exact s4_13
      linear_combination (norm := parley_field) (-((3 ^ m) ^ 2 * 9 ^ m)) * s4_11
  -- 5. thm:positive-power-is-real a := 3
  have r191_1 : (3 : ℤ) > 0 := by parley_arith
  -- 6. algebra, from 3, 4, 5
  linear_combination (norm := parley_norm) (-1) * s3 + s4

end Parley.Proofs.Hammack.NinePowersAndThreePowers.NinePowerIsThreePower
