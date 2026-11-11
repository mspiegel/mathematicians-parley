module

public import SetTactics
public import SubstTactics
public import Tactics
public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.Set
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Sets

/-! Written from tests/elaborator/a-define-put-into-a-line.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ADefinePutIntoALine.ADefinePutIntoALine

theorem a_define_put_into_a_line {α : Type*} (A : Set α) (B : Set α) :
    A ∩ B ⊆ A := by
  set C : Set α := A ∩ B with hD1
  -- 1. mun:intersection-subset Y := A, Z := B, from D1
  have s1 : C ⊆ A := by
    try simp only [hD1] at ⊢
    try push_cast at ⊢
    exact (Parley.Items.Stdlib.Sets.mun_intersection_subset (Y := A) (Z := B))
  -- 2. substitute C = A ∩ B (D1) into line 1
  parley_subst_at hD1 s1

end Parley.Tests.Elaborator.ADefinePutIntoALine.ADefinePutIntoALine
