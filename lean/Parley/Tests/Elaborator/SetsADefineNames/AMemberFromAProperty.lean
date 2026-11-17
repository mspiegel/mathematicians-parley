module

public import Batteries.Util.ExtendedBinder
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Sets

/-! Written from tests/elaborator/sets-a-define-names.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.SetsADefineNames.AMemberFromAProperty

theorem a_member_from_a_property (T : Set ℤ) (N : ℤ) (hH1 : 0 < N) (hH3 : T ∈ {S ∈ 𝒫 (Set.Icc (1 : ℤ) N : Set ℤ) | N ∈ S ∧ (∀ p ∈ S, p ≤ N)}) :
    N ∈ T := by
  -- 1. def:part-builder u := T, from H3
  exact ((((Parley.Items.Stdlib.Sets.def_part_builder (P := (fun S : Set ℤ => N ∈ S ∧ (∀ p ∈ S, p ≤ N))) (X := (Set.Icc (1 : ℤ) N : Set ℤ)) (u := T))).mp hH3).2).1

end Parley.Tests.Elaborator.SetsADefineNames.AMemberFromAProperty
