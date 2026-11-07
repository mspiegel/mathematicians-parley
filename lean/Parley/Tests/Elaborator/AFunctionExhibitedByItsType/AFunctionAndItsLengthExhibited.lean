module

public import SetTactics
public import Tactics
public import WholeTactics
public import Batteries.Util.ExtendedBinder
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Set
public import Parley.Items.Stdlib.Functions

/-! Written from tests/elaborator/a-function-exhibited-by-its-type.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AFunctionExhibitedByItsType.AFunctionAndItsLengthExhibited

theorem a_function_and_its_length_exhibited (n : ℤ) (hH1 : 0 < n) :
    (∃ k : ℤ, 0 < k ∧ (∃ f : ℤ → ℤ, Set.MapsTo f (Set.Icc (1 : ℤ) k : Set ℤ) {n : ℤ | 0 < n} ∧ (∀ i : ℤ, i ∈ Finset.Icc 1 k → f i = 1))) := by
  set g : ℤ → ℤ := fun i => (1 : ℤ) with hD1
  -- 1. D1
  have s1 : ∀ i : ℤ, i ∈ Finset.Icc 1 n → g i = 1 := by first | (simp (disch := omega) only [hD1]; done) | (simp (disch := omega) only [hD1]; push_cast; norm_num; done) | parley_set_side
  -- 2. membership, from D1
  have s2 : ∀ i : ℤ, i ∈ Finset.Icc 1 n → 0 < g i := by intro i h_i; parley_set_side
  -- 3. mun:function-into, from 2
  have s3 : Set.MapsTo g (Set.Icc (1 : ℤ) n : Set ℤ) {n : ℤ | 0 < n} := by exact (Parley.Items.Stdlib.Functions.mun_function_into (E := g) (X := (Set.Icc (1 : ℤ) n : Set ℤ)) (Y := {n : ℤ | 0 < n}) (by parley_set_side) (by parley_whole_side))
  -- 4. exhibit, from 1, 3
  have s4 : ∃ k : ℤ, 0 < k ∧ (∃ f : ℤ → ℤ, Set.MapsTo f (Set.Icc (1 : ℤ) k : Set ℤ) {n : ℤ | 0 < n} ∧ (∀ i : ℤ, i ∈ Finset.Icc 1 k → f i = 1)) := ⟨n, by parley_set_side, g, by parley_set_side, by parley_set_side⟩
  all_goals exact s4

end Parley.Tests.Elaborator.AFunctionExhibitedByItsType.AFunctionAndItsLengthExhibited
