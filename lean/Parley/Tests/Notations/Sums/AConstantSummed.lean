module

public import ArithTactics
public import NormTactics
public import PowerTactics
public import Tactics
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.BigOperators
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Parley.Items.Stdlib.Sums

/-! Written from tests/notations/sums.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Sums.AConstantSummed

theorem a_constant_summed :
    (∑ k ∈ Finset.Icc (1 : ℤ) (3 : ℤ), (5 : ℤ)) = 15 := by
  -- 1. mun:sum-constant a := 1, b := 3, c := 5
  have r11_1 : (1 : ℤ) ≤ 3 := by parley_arith
  have s1 : (∑ k ∈ Finset.Icc (1 : ℤ) (3 : ℤ), (5 : ℤ)) = (3 - 1 + 1) * 5 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_sum_constant (a := (1 : ℤ)) (b := (3 : ℤ)) (by parley_side) (c := (5 : ℤ))) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_constant (a := (1 : ℤ)) (b := (3 : ℤ)) (by parley_side) (c := (5 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_constant (a := (1 : ℤ)) (b := (3 : ℤ)) (by parley_side) (c := (5 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_sum_constant (a := (1 : ℤ)) (b := (3 : ℤ)) (by parley_side) (c := (5 : ℤ))) | exact_mod_cast ((Parley.Items.Stdlib.Sums.mun_sum_constant (a := (1 : ℤ)) (b := (3 : ℤ)) (by parley_side) (c := (5 : ℤ)))).symm | (have h := (Parley.Items.Stdlib.Sums.mun_sum_constant (a := (1 : ℤ)) (b := (3 : ℤ)) (by parley_side) (c := (5 : ℤ))); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_constant (a := (1 : ℤ)) (b := (3 : ℤ)) (by parley_side) (c := (5 : ℤ))); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_constant (a := (1 : ℤ)) (b := (3 : ℤ)) (by parley_side) (c := (5 : ℤ))); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_constant (a := (1 : ℤ)) (b := (3 : ℤ)) (by parley_side) (c := (5 : ℤ))); parley_side)
  -- 2. calculation
  have s2 : (∑ k ∈ Finset.Icc (1 : ℤ) (3 : ℤ), (5 : ℤ)) = 15 := by
    calc (∑ k ∈ Finset.Icc (1 : ℤ) (3 : ℤ), (5 : ℤ)) = (3 - 1 + 1) * 5 := by parley_side
      _ = 15 := by norm_num
  all_goals exact s2

end Parley.Tests.Notations.Sums.AConstantSummed
