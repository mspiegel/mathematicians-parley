module

public import Tactics
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.ENat.Basic
public import Mathlib.Data.ENat.Defs
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq

/-! Written from proofs/wiedijk/ballot.proof by parley build lean. -/

public section

namespace Parley.Items.Proofs.Wiedijk.Ballot

theorem def_ahead (c : Set ℤ) (k : ℤ) :
    (∀ i : ℤ, i ∈ Finset.Icc 1 k → ((Set.Icc (1 : ℤ) i : Set ℤ) \ c).encard < ((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).encard) ↔ (∀ i : ℤ, i ∈ Finset.Icc 1 k → ((Set.Icc (1 : ℤ) i : Set ℤ) \ c).encard < ((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).encard) :=
  Iff.rfl

end Parley.Items.Proofs.Wiedijk.Ballot
