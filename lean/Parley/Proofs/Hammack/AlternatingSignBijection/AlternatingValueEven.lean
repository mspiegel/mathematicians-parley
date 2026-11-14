module

public import Mathlib.Algebra.Group.Even
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Rat.Init
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Ring.RingNF
public import Parley.Proofs.Hammack.AlternatingSignBijection.SignOfEven

/-! Written from proofs/hammack/alternating-sign-bijection.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.AlternatingSignBijection.AlternatingValueEven

theorem alternating_value_even (f : ℤ → ℤ) (hH2 : ∀ n : ℤ, 0 < n → (f n : ℚ) = ((-1) ^ n.toNat * (2 * (n : ℚ) - 1) + 1) / 4) (m : ℤ) (hH3 : 0 < m) (hH4 : Even m) :
    (f m : ℚ) = (m : ℚ) / 2 := by
  -- 1. thm:sign-of-even n := m, from H4
  have s1 : ((-1) ^ m.toNat : ℤ) = 1 := by exact (Parley.Proofs.Hammack.AlternatingSignBijection.SignOfEven.sign_of_even (n := m) hH3 hH4)
  -- 2. calculation
  calc (f m : ℚ) = ((-1) ^ m.toNat * (2 * (m : ℚ) - 1) + 1) / 4 := by exact (hH2 m hH3)
    _ = (1 * (2 * (m : ℚ) - 1) + 1) / 4 := by
        have e_w : ((-1) ^ m.toNat : ℚ) = 1 := by have h := congrArg (fun x : ℤ => (x : ℚ)) s1; push_cast at h ⊢; linear_combination h
        exact congrArg (fun t : ℚ => (t * (2 * (m : ℚ) - 1) + 1) / 4) e_w
    _ = (m : ℚ) / 2 := by ring_nf

end Parley.Proofs.Hammack.AlternatingSignBijection.AlternatingValueEven
