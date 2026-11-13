module

public import SetTactics
public import Tactics
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Groups

/-! Written from tests/notations/groups.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Groups.ASubgroupTest

theorem a_subgroup_test {G : Type*} [Group G] (H : Subgroup G) (a : G) (hH3 : a ∈ (H : Set G)) (b : G) (hH4 : b ∈ (H : Set G)) :
    a * b⁻¹ ∈ (H : Set G) := by
  -- 1. mun:subgroup-inverse a := b, from H2, H4
  have s1 : b⁻¹ ∈ (H : Set G) := by exact (Parley.Items.Stdlib.Groups.mun_subgroup_inverse (G := G) (H := H) (a := b) hH4)
  -- 2. mun:subgroup-closed b := b⁻¹, from H2, H3, 1
  exact (Parley.Items.Stdlib.Groups.mun_subgroup_closed (G := G) (H := H) (a := a) hH3 (b := b⁻¹) s1)

end Parley.Tests.Notations.Groups.ASubgroupTest
