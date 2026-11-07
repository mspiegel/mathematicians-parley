module

public import Tactics
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.TypeStar

/-! Written from proofs/wiedijk/pythagorean-triples.proof by parley build lean. -/

public section

namespace Parley.Items.Proofs.Wiedijk.PythagoreanTriples

theorem def_euclid_hypotenuse {K : Type*} [CommRing K] [IsDomain K] [CharZero K] (a : K) (b : K) (c : K) :
    (∃ k : ℤ, 0 < k ∧ (∃ m : ℤ, 0 < m ∧ (∃ n : ℤ, 0 < n ∧ (c = (k : K) * ((m : K) ^ 2 + (n : K) ^ 2) ∧ ({a, b} : Set K) = ({(k : K) * ((m : K) ^ 2 - (n : K) ^ 2), 2 * (k : K) * (m : K) * (n : K)} : Set K))))) ↔ (∃ k : ℤ, 0 < k ∧ (∃ m : ℤ, 0 < m ∧ (∃ n : ℤ, 0 < n ∧ (c = (k : K) * ((m : K) ^ 2 + (n : K) ^ 2) ∧ ({a, b} : Set K) = ({(k : K) * ((m : K) ^ 2 - (n : K) ^ 2), 2 * (k : K) * (m : K) * (n : K)} : Set K))))) :=
  Iff.rfl

end Parley.Items.Proofs.Wiedijk.PythagoreanTriples
