module

public import AlgebraTactics
public import NormTactics
public import SubstTactics
public import Tactics
public import Mathlib.Algebra.Group.Even
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Rat.Init
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Proofs.Hammack.AlternatingSignBijection.SignOfEven

/-! Written from proofs/hammack/alternating-sign-bijection.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.AlternatingSignBijection.AlternatingValueEven

theorem alternating_value_even (f : ℤ → ℤ) (hH2 : ∀ n : ℤ, 0 < n → (f n : ℚ) = ((-1) ^ n.toNat * (2 * (n : ℚ) - 1) + 1) / 4) (m : ℤ) (hH3 : 0 < m) (hH4 : Even m) :
    (f m : ℚ) = (m : ℚ) / 2 := by
  -- 1. thm:sign-of-even n := m, from H4
  have s1 : ((-1) ^ m.toNat : ℤ) = 1 := by exact (Parley.Proofs.Hammack.AlternatingSignBijection.SignOfEven.sign_of_even (n := m) (by parley_side) hH4)
  -- 2. calculation
  calc (f m : ℚ) = ((-1) ^ m.toNat * (2 * (m : ℚ) - 1) + 1) / 4 := by exact (hH2 m (by parley_side))
    _ = (1 * (2 * (m : ℚ) - 1) + 1) / 4 := by
        have s1_w : ((-1) ^ m.toNat : ℚ) = 1 := by have h := congrArg (fun x : ℤ => (x : ℚ)) s1; push_cast at h; linear_combination (norm := parley_norm) h
        first | parley_subst s1_w | parley_subst s1
    _ = (m : ℚ) / 2 := by parley_ring

end Parley.Proofs.Hammack.AlternatingSignBijection.AlternatingValueEven
