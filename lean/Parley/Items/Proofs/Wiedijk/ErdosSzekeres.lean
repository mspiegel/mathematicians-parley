module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.ENat.Basic
public import Mathlib.Data.ENat.Defs
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq

/-! Written from proofs/wiedijk/erdos-szekeres.proof by parley build lean. -/

public section

namespace Parley.Items.Proofs.Wiedijk.ErdosSzekeres

theorem def_rising_run (S : Set ℝ) (a : ℝ → ℝ) (n : ℕ) :
    ((n : ℕ) : ℕ∞) ≤ S.encard ∧ (∀ i ∈ S, ∀ j ∈ S, i < j → a i < a j) ↔ ((n : ℕ) : ℕ∞) ≤ S.encard ∧ (∀ i ∈ S, ∀ j ∈ S, i < j → a i < a j) :=
  Iff.rfl

theorem def_falling_run (S : Set ℝ) (a : ℝ → ℝ) (n : ℕ) :
    ((n : ℕ) : ℕ∞) ≤ S.encard ∧ (∀ i ∈ S, ∀ j ∈ S, i < j → a j < a i) ↔ ((n : ℕ) : ℕ∞) ≤ S.encard ∧ (∀ i ∈ S, ∀ j ∈ S, i < j → a j < a i) :=
  Iff.rfl

end Parley.Items.Proofs.Wiedijk.ErdosSzekeres
