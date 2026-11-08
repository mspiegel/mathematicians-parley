module

public import AlgebraTactics
public import SetTactics
public import SubstTactics
public import Tactics
public import Batteries.Util.ExtendedBinder
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/elaborator/a-define-applied-in-a-hypothesis.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ADefineAppliedInAHypothesis.AHypothesisSubstitutedInto

theorem a_hypothesis_substituted_into (m : ℤ) (hH1 : 0 < m) (n : ℤ) (hH2 : 0 < n) (hH3 : ({d ∈ 𝒫 (Set.Icc (1 : ℤ) (m - 1 + n) : Set ℤ) | (d.ncard : ℤ) = m - 1}.ncard : ℤ) * (m - 1 + n) = 0) :
    ({d ∈ 𝒫 (Set.Icc (1 : ℤ) (m - 1 + n) : Set ℤ) | (d.ncard : ℤ) = m - 1}.ncard : ℤ) * (m + (n - 1)) = 0 := by
  -- 1. mun:nat-minus-one n := m
  have s1 : 0 ≤ m - 1 := by exact (Parley.Items.Stdlib.Numbers.mun_nat_minus_one (n := m) (by parley_set_side))
  -- 2. algebra
  have s2 : m - 1 + n = m + (n - 1) := by parley_ring
  -- 3. substitute (m − 1) + n = m + (n − 1) (line 2) into H3
  have r21_1 : 0 ≤ m - 1 := by parley_set_side
  parley_subst_at s2 hH3

end Parley.Tests.Elaborator.ADefineAppliedInAHypothesis.AHypothesisSubstitutedInto
