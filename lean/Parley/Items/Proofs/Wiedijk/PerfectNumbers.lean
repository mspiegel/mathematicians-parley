module

public import Tactics
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic

/-! Written from proofs/wiedijk/perfect-numbers.proof by parley build lean. -/

public section

namespace Parley.Items.Proofs.Wiedijk.PerfectNumbers

theorem def_power_times_odd (j : ℂ) :
    (∃ k : ℤ, 0 ≤ k ∧ (∃ m : ℤ, 0 < m ∧ (Odd m ∧ j = 2 ^ k.toNat * (m : ℂ)))) ↔ (∃ k : ℤ, 0 ≤ k ∧ (∃ m : ℤ, 0 < m ∧ (Odd m ∧ j = 2 ^ k.toNat * (m : ℂ)))) :=
  Iff.rfl

end Parley.Items.Proofs.Wiedijk.PerfectNumbers
