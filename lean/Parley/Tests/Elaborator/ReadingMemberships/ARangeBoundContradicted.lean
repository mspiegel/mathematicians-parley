module

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

/-! Written from tests/elaborator/reading-memberships.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingMemberships.ARangeBoundContradicted

theorem a_range_bound_contradicted (n : ℤ) (k : ℤ) (hH2 : k ∈ Finset.Icc (1 : ℤ) n) :
    ¬ n < k := by
  -- 1. contradiction
  intro hS
  -- 1.1. inequalities, from S
  have s1_1 : ¬ k ≤ n := by linarith only [hS]
  exact s1_1 (Finset.mem_Icc.mp hH2).2

end Parley.Tests.Elaborator.ReadingMemberships.ARangeBoundContradicted
