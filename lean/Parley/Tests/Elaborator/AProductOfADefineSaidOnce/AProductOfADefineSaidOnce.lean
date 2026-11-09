module

public import SetTactics
public import Tactics
public import WholeTactics
public import Batteries.Util.ExtendedBinder
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.BigOperators
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Set
public import Parley.Items.Stdlib.Functions
public import Parley.Items.Stdlib.Sums

/-! Written from tests/elaborator/a-product-of-a-define-said-once.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AProductOfADefineSaidOnce.AProductOfADefineSaidOnce

theorem a_product_of_a_define_said_once (p : ℤ) (hH1 : 0 < p) :
    (∃ f : ℤ → ℤ, Set.MapsTo f (Set.Icc (1 : ℤ) (1 : ℤ) : Set ℤ) {n : ℤ | 0 < n} ∧ p = (∏ i ∈ Finset.Icc (1 : ℤ) (1 : ℤ), (f i : ℤ))) := by
  set e : ℤ → ℤ := fun i : ℤ => p with hD1
  -- 1. mun:product-single a := 1, t := e
  have s1 : (∏ i ∈ Finset.Icc (1 : ℤ) (1 : ℤ), (e i : ℤ)) = e 1 := (Parley.Items.Stdlib.Sums.mun_product_single (t := e) (a := (1 : ℤ)))
  -- 2. D1
  have r15_1 : (1 : ℤ) ∈ Finset.Icc (1 : ℤ) (1 : ℤ) := by parley_set_side
  have s2 : e 1 = p := by simp (disch := omega) only [hD1]
  -- 3. calculation
  have s3 : p = (∏ i ∈ Finset.Icc (1 : ℤ) (1 : ℤ), (e i : ℤ)) := by
    calc p = e 1 := by parley_set_side
      _ = (∏ i ∈ Finset.Icc (1 : ℤ) (1 : ℤ), (e i : ℤ)) := by parley_set_side
  -- 4. membership, from D1
  have s4 : ∀ i : ℤ, i ∈ Finset.Icc 1 1 → 0 < e i := by intro i h_i; parley_set_side
  -- 5. mun:function-into, from 4
  have s5 : Set.MapsTo e (Set.Icc (1 : ℤ) (1 : ℤ) : Set ℤ) {n : ℤ | 0 < n} := by exact (Parley.Items.Stdlib.Functions.mun_function_into (E := e) (X := (Set.Icc (1 : ℤ) (1 : ℤ) : Set ℤ)) (Y := {n : ℤ | 0 < n}) (by parley_set_side) (by parley_whole_side))
  -- 6. exhibit, from 3, 5
  exact ⟨e, by parley_set_side, by parley_set_side⟩

end Parley.Tests.Elaborator.AProductOfADefineSaidOnce.AProductOfADefineSaidOnce
