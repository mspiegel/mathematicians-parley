module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.SetNotationForOrder
public import Parley.Items.Tests.Elaborator.APhraseWithAWherePart

/-! Written from tests/elaborator/a-phrase-with-a-where-part.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.APhraseWithAWherePart.ARisingRunIsLong

theorem a_rising_run_is_long (N : ℤ) (hH1 : 0 < N) (r : ℤ) (hH2 : 0 < r) (a : ℤ → ℝ) (hH3 : Set.MapsTo a (Set.Icc (1 : ℤ) N : Set ℤ) (Set.univ : Set ℝ) ∧ Set.InjOn a (Set.Icc (1 : ℤ) N : Set ℤ)) (S : Set ℤ) (hH4 : S ⊆ (Set.Icc (1 : ℤ) N : Set ℤ)) (hH5 : r ≤ (S.ncard : ℤ) ∧ (∀ i ∈ S, ∀ j ∈ S, i < j → a i < a j)) :
    r ≤ (S.ncard : ℤ) := by
  -- 1. D2, from H5
  have s1 : r ≤ (S.ncard : ℤ) ∧ (∀ i ∈ S, ∀ j ∈ S, i < j → a i < a j) := hH5
  -- 2. restate 1
  exact s1.1

end Parley.Tests.Elaborator.APhraseWithAWherePart.ARisingRunIsLong
