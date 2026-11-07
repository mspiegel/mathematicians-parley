module

public import AlgebraTactics
public import NormTactics
public import PowerTactics
public import SubstTactics
public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Even
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Rat.Init
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Parley.Proofs.Hammack.AlternatingSignBijection.SignOfEven

/-! Written from proofs/hammack/alternating-sign-bijection.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.AlternatingSignBijection.AlternatingValueEven

theorem alternating_value_even (f : ℤ → ℤ) (hH2 : ∀ n : ℤ, 0 < n → (f n : ℚ) = ((-1) ^ n.toNat * (2 * (n : ℚ) - 1) + 1) / 4) (m : ℤ) (hH3 : 0 < m) (hH4 : Even m) :
    (f m : ℚ) = (m : ℚ) / 2 := by
  -- 1. thm:sign-of-even n := m, from H4
  have s1 : ((-1) ^ m.toNat : ℤ) = 1 := by first | linear_combination (norm := parley_norm) (Parley.Proofs.Hammack.AlternatingSignBijection.SignOfEven.sign_of_even (n := m) (by parley_side) hH4) | (have h := (Parley.Proofs.Hammack.AlternatingSignBijection.SignOfEven.sign_of_even (n := m) (by parley_side) hH4); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Hammack.AlternatingSignBijection.SignOfEven.sign_of_even (n := m) (by parley_side) hH4); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Proofs.Hammack.AlternatingSignBijection.SignOfEven.sign_of_even (n := m) (by parley_side) hH4) | exact_mod_cast ((Parley.Proofs.Hammack.AlternatingSignBijection.SignOfEven.sign_of_even (n := m) (by parley_side) hH4)).symm | (have h := (Parley.Proofs.Hammack.AlternatingSignBijection.SignOfEven.sign_of_even (n := m) (by parley_side) hH4); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Hammack.AlternatingSignBijection.SignOfEven.sign_of_even (n := m) (by parley_side) hH4); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Hammack.AlternatingSignBijection.SignOfEven.sign_of_even (n := m) (by parley_side) hH4); parley_int_power h) | (have h := (Parley.Proofs.Hammack.AlternatingSignBijection.SignOfEven.sign_of_even (n := m) (by parley_side) hH4); simp (disch := omega) only [← zpow_natCast, Int.toNat_of_nonneg] at h ⊢; exact h) | (have h := (Parley.Proofs.Hammack.AlternatingSignBijection.SignOfEven.sign_of_even (n := m) (by parley_side) hH4); simp +contextual (disch := (simp only [Finset.mem_Icc] at *; first | omega | positivity | nlinarith)) only [parley_zpow_toNat] at h ⊢; first | exact h | exact_mod_cast h | linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Hammack.AlternatingSignBijection.SignOfEven.sign_of_even (n := m) (by parley_side) hH4); parley_side)
  -- 2. calculation
  have s2 : (f m : ℚ) = (m : ℚ) / 2 := by
    calc (f m : ℚ) = ((-1) ^ m.toNat * (2 * (m : ℚ) - 1) + 1) / 4 := by first | linear_combination (norm := parley_norm) (hH2 m (by parley_side)) | (have h := (hH2 m (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (hH2 m (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (hH2 m (by parley_side)) | exact_mod_cast ((hH2 m (by parley_side))).symm | (have h := (hH2 m (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (hH2 m (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (hH2 m (by parley_side)); parley_int_power h) | (have h := (hH2 m (by parley_side)); simp (disch := omega) only [← zpow_natCast, Int.toNat_of_nonneg] at h ⊢; exact h) | (have h := (hH2 m (by parley_side)); simp +contextual (disch := (simp only [Finset.mem_Icc] at *; first | omega | positivity | nlinarith)) only [parley_zpow_toNat] at h ⊢; first | exact h | exact_mod_cast h | linear_combination (norm := parley_norm) h) | (have h := (hH2 m (by parley_side)); parley_side)
      _ = (1 * (2 * (m : ℚ) - 1) + 1) / 4 := by
          have s1_w : ((-1) ^ m.toNat : ℚ) = 1 := by have h := congrArg (fun x : ℤ => (x : ℚ)) s1; push_cast at h; linear_combination (norm := parley_norm) h
          first | parley_subst s1_w | parley_subst s1
      _ = (m : ℚ) / 2 := by parley_ring
  all_goals exact s2

end Parley.Proofs.Hammack.AlternatingSignBijection.AlternatingValueEven
