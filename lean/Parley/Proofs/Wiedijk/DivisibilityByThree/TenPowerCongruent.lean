module

public import Functions
public import NormTactics
public import PowerTactics
public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Positivity.Core
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
      simpa using s1_1
    | succ m hK hIH =>
      -- 1.2. mun:exponent-step a := 10
      have s1_2 : (10 ^ (m + 1).toNat : ℤ) = 10 ^ m.toNat * 10 := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (10 : ℤ)) (m := m) (by parley_side))
      -- 1.3. calculation
      calc (10 ^ (m + 1).toNat : ℤ) = 10 ^ m.toNat * 10 := by first | parley_side | parley_line_toNat s1_2
        _ ≡ 1 * 10 [ZMOD (3 : ℤ)] := (Parley.Proofs.Wiedijk.DivisibilityByThree.CongruentTimes.congruent_times (a := (10 ^ m.toNat : ℤ)) (b := (1 : ℤ)) (c := (10 : ℤ)) (n := (3 : ℤ)) (by parley_side) hIH)
        _ ≡ 10 [ZMOD (3 : ℤ)] := by norm_num
        _ ≡ 1 [ZMOD (3 : ℤ)] := by norm_num
  -- 2. instantiate m := k in line 1
  first | exact (s1 k (by parley_side)) | exact ((s1 k (by parley_side))).symm | simpa using (s1 k (by parley_side)) | exact_mod_cast (s1 k (by parley_side)) | (have h := (s1 k (by parley_side)); simp (disch := omega) only [← zpow_natCast, Int.toNat_of_nonneg] at h ⊢; exact h) | (have h := (s1 k (by parley_side)); simp +contextual (disch := (simp only [Finset.mem_Icc] at *; first | omega | positivity | nlinarith)) only [parley_zpow_toNat] at h ⊢; first | exact h | exact_mod_cast h | linear_combination (norm := parley_norm) h) | (have h := (s1 k (by parley_side)); parley_side)

end Parley.Proofs.Wiedijk.DivisibilityByThree.TenPowerCongruent
