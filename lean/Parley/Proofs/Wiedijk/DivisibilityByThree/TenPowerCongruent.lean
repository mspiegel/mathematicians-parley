module

public import Functions
public import Tactics
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers
public import Parley.Proofs.Wiedijk.DivisibilityByThree.CongruentTimes

/-! Written from proofs/wiedijk/divisibility-by-three.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.DivisibilityByThree.TenPowerCongruent

theorem ten_power_congruent (k : ℤ) (hH1 : 0 ≤ k) :
    (10 ^ k.toNat : ℤ) ≡ (1 : ℤ) [ZMOD (3 : ℤ)] := by
  -- 1. induction on m starting at 0
  have s1 : ∀ m : ℤ, 0 ≤ m → (10 ^ m.toNat : ℤ) ≡ (1 : ℤ) [ZMOD (3 : ℤ)] := by
    intro m h_m
    replace h_m : 0 ≤ m := by omega
    induction m, h_m using LeanBridges.Functions.le_induction with
    | base =>
      -- 1.1. calculation
      have s1_1 : (10 ^ 0 : ℤ) ≡ (1 : ℤ) [ZMOD (3 : ℤ)] := by
        calc (10 ^ 0 : ℤ) = 1 := by norm_num
          _ ≡ 1 [ZMOD (3 : ℤ)] := by norm_num
      simpa only [Int.reduceToNat, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Int.cast_ofNat, Int.cast_zero, Int.cast_one] using s1_1
    | succ m hK hIH =>
      -- 1.2. mun:exponent-step a := 10
      have s1_2 : (10 ^ (m + 1).toNat : ℤ) = 10 ^ m.toNat * 10 := by exact (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (10 : ℤ)) (m := m) (by parley_side))
      -- 1.3. calculation
      calc (10 ^ (m + 1).toNat : ℤ) = 10 ^ m.toNat * 10 := by exact s1_2
        _ ≡ 1 * 10 [ZMOD (3 : ℤ)] := by exact (Parley.Proofs.Wiedijk.DivisibilityByThree.CongruentTimes.congruent_times (a := (10 ^ m.toNat : ℤ)) (b := (1 : ℤ)) (c := (10 : ℤ)) (n := (3 : ℤ)) (by parley_side) hIH)
        _ ≡ 10 [ZMOD (3 : ℤ)] := by norm_num
        _ ≡ 1 [ZMOD (3 : ℤ)] := by norm_num
  -- 2. instantiate m := k in line 1
  exact (s1 k (by parley_side))

end Parley.Proofs.Wiedijk.DivisibilityByThree.TenPowerCongruent
