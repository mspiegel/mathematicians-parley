module

public import SetTactics
public import Tactics
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

namespace Parley.Tests.Elaborator.AFunctionExhibitedByItsType.AFunctionExhibitedByItsType

theorem a_function_exhibited_by_its_type (n : ℤ) (hH1 : 0 < n) :
    (∃ f : ℤ → ℤ, Set.MapsTo f (Set.Icc (1 : ℤ) n : Set ℤ) {n : ℤ | 0 < n} ∧ (∀ i : ℤ, i ∈ Finset.Icc 1 n → f i = 1)) := by
  set g : ℤ → ℤ := fun i : ℤ => (1 : ℤ) with hD1
  -- 1. D1
  have s1 : ∀ i : ℤ, i ∈ Finset.Icc 1 n → g i = 1 := by simp (disch := omega) only [hD1, implies_true]
  -- 2. membership, from D1
  have s2 : ∀ i : ℤ, i ∈ Finset.Icc 1 n → 0 < g i := by intro i h_i; exact by rw [hD1]; exact by norm_num
  -- 3. mun:function-into, from 2
  have s3 : Set.MapsTo g (Set.Icc (1 : ℤ) n : Set ℤ) {n : ℤ | 0 < n} := by exact (Parley.Items.Stdlib.Functions.mun_function_into (E := g) (X := (Set.Icc (1 : ℤ) n : Set ℤ)) (Y := {n : ℤ | 0 < n}) (by simpa only [Finset.mem_Icc, Set.mem_Icc, Set.mem_ofPred_eq] using s2))
  -- 4. exhibit, from 1, 3
  exact ⟨g, s3, s1⟩

end Parley.Tests.Elaborator.AFunctionExhibitedByItsType.AFunctionExhibitedByItsType
