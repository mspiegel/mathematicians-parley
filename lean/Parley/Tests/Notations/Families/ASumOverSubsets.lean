module

public import SetTactics
public import Tactics
public import Batteries.Util.ExtendedBinder
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Sums

/-! Written from tests/notations/families.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Families.ASumOverSubsets

theorem a_sum_over_subsets {α : Type*} (D : Set α) (K : Set (Set α)) (hH2 : K ⊆ 𝒫 D) (hH3 : K.Finite) :
    (∑ᶠ s ∈ K, (1 : ℤ)) = (K.ncard : ℤ) * 1 := by
  -- 1. mun:sum-constant-over X := K, c := 1, from H3
  exact (Parley.Items.Stdlib.Sums.mun_sum_constant_over (X := K) hH3 (c := (1 : ℤ)))

end Parley.Tests.Notations.Families.ASumOverSubsets
