module

public import OrderTactics
public import SetTactics
public import Tactics
public import Batteries.Util.ExtendedBinder
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.NumberTheory.ArithmeticFunction.Defs
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.SetNotationForOrder
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Sets
public import Parley.Items.Stdlib.Sums

/-! Written from proofs/wiedijk/perfect-numbers.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.PerfectNumbers.ThreeDivisors

theorem three_divisors (m : ℤ) (hH1 : 0 < m) (e : ℤ) (hH2 : 0 < e) (hH3 : e ∣ m) (hH4 : 1 < e) (hH5 : e < m) :
    (ArithmeticFunction.sigma 1 m.toNat : ℤ) ≥ 1 + e + m := by
  -- 1. mun:one-divides n := m
  have s1 : (1 : ℤ) ∣ m := by exact (Parley.Items.Stdlib.Divisibility.mun_one_divides (n := m))
  -- 2. mun:divides-self n := m
  have s2 : m ∣ m := by exact (Parley.Items.Stdlib.Divisibility.mun_divides_self (n := m))
  -- 3. def:set-builder u := 1, from 1
  have s3 : (1 : ℤ) ∈ {d : ℤ | 0 < d ∧ d ∣ m} := by simpa only [Int.cast_id, Set.mem_sep_iff, Set.mem_setOf_eq] using ((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun d : ℤ => d ∣ m)) (X := {n : ℤ | 0 < n}) (u := (1 : ℤ)))).mpr (by parley_set_side)
  -- 4. def:set-builder u := e, from H3
  have s4 : e ∈ {d : ℤ | 0 < d ∧ d ∣ m} := by simpa only [Int.cast_id, Set.mem_sep_iff, Set.mem_setOf_eq] using ((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun d : ℤ => d ∣ m)) (X := {n : ℤ | 0 < n}) (u := e))).mpr (by parley_set_side)
  -- 5. def:set-builder u := m, from 2
  have s5 : m ∈ {d : ℤ | 0 < d ∧ d ∣ m} := by simpa only [Int.cast_id, Set.mem_sep_iff, Set.mem_setOf_eq] using ((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun d : ℤ => d ∣ m)) (X := {n : ℤ | 0 < n}) (u := m))).mpr (by parley_set_side)
  -- 6. mun:triple-subset, from 3, 4, 5
  have s6 : ({(1 : ℤ), e, m} : Set ℤ) ⊆ {d : ℤ | 0 < d ∧ d ∣ m} := by exact (Parley.Items.Stdlib.Sets.mun_triple_subset (X := {d : ℤ | 0 < d ∧ d ∣ m}) (a := (1 : ℤ)) (b := e) (c := m) s3 s4 s5)
  -- 7. transitivity, from H4, H5
  have s7 : 1 < m := by parley_order
  -- 8. calculation
  have r302_1 : 1 ≠ e := by parley_set_side
  have r302_2 : 1 ≠ m := by parley_set_side
  have r302_3 : e ≠ m := by parley_set_side
  calc (ArithmeticFunction.sigma 1 m.toNat : ℤ) ≥ (∑ᶠ d ∈ ({(1 : ℤ), e, m} : Set ℤ), (d : ℤ)) := by exact (Parley.Items.Stdlib.Divisibility.mun_sigma_part (Y := ({(1 : ℤ), e, m} : Set ℤ)) (n := m) (by parley_set_side) s6)
    _ = 1 + e + m := by exact (Parley.Items.Stdlib.Sums.mun_sum_of_three (a := (1 : ℤ)) (b := e) (c := m) (by parley_set_side) (by parley_set_side) (by parley_set_side))

end Parley.Proofs.Wiedijk.PerfectNumbers.ThreeDivisors
