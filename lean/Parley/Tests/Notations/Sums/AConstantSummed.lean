module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.BigOperators
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Sums

/-! Written from tests/notations/sums.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Sums.AConstantSummed

theorem a_constant_summed :
    (∑ k ∈ Finset.Icc (1 : ℤ) (3 : ℤ), (5 : ℤ)) = 15 := by
  -- 1. mun:sum-constant a := 1, b := 3, c := 5
  have r11_1 : (1 : ℤ) ≤ 3 := by norm_num
  have s1 : (∑ k ∈ Finset.Icc (1 : ℤ) (3 : ℤ), (5 : ℤ)) = (3 - 1 + 1) * 5 := by exact (Parley.Items.Stdlib.Sums.mun_sum_constant (a := (1 : ℤ)) (b := (3 : ℤ)) (by norm_num) (c := (5 : ℤ)))
  -- 2. calculation
  calc (∑ k ∈ Finset.Icc (1 : ℤ) (3 : ℤ), (5 : ℤ)) = (3 - 1 + 1) * 5 := s1
    _ = 15 := by norm_num

end Parley.Tests.Notations.Sums.AConstantSummed
