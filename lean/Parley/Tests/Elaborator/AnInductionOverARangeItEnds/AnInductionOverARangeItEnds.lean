module

public import Functions
public import Tactics
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Sums

/-! Written from tests/elaborator/an-induction-over-a-range-it-ends.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AnInductionOverARangeItEnds.AnInductionOverARangeItEnds

theorem an_induction_over_a_range_it_ends (n : ℤ) (hH1 : 0 ≤ n) :
    (∀ j : ℤ, j ∈ Finset.Icc 1 n → j ≥ 1) := by
  -- 1. induction on N starting at 0
  have s1 : ∀ N : ℤ, 0 ≤ N → (∀ j : ℤ, j ∈ Finset.Icc 1 N → j ≥ 1) := by
    intro N h_N
    replace h_N : 0 ≤ N := by omega
    induction N, h_N using LeanBridges.Functions.le_induction with
    | base =>
      -- 1.1. proof
      intro j hK1
      try push_cast at hK1
      try have hK1_bounds := Finset.mem_Icc.mp hK1
      -- 1.1.1. mun:range-bounds a := 1, b := 0, k := j, from K1
      have s1_1_1 : 1 ≤ j := by exact (Parley.Items.Stdlib.Sums.mun_range_bounds_1 (a := (1 : ℤ)) (b := (0 : ℤ)) (k := j) hK1)
      -- 1.1.2. inequalities, from 1.1.1
      linarith only [s1_1_1]
    | succ N hK2 hIH =>
      -- 1.2. proof
      intro j hK3
      try push_cast at hK3
      try have hK3_bounds := Finset.mem_Icc.mp hK3
      -- 1.2.1. mun:range-bounds a := 1, b := N + 1, k := j, from K3
      have s1_2_1 : 1 ≤ j := by exact (Parley.Items.Stdlib.Sums.mun_range_bounds_1 (a := (1 : ℤ)) (b := N + 1) (k := j) hK3)
      -- 1.2.2. inequalities, from 1.2.1
      linarith only [s1_2_1]
  -- 2. instantiate N := n in line 1
  intro j h_j; exact (s1 n hH1 j (by parley_side))

end Parley.Tests.Elaborator.AnInductionOverARangeItEnds.AnInductionOverARangeItEnds
