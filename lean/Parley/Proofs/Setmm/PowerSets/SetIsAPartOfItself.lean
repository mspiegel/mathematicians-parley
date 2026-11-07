module

public import SetTactics
public import Tactics
public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/setmm/power-sets.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.PowerSets.SetIsAPartOfItself

theorem set_is_a_part_of_itself {α : Type*} (A : Set α) :
    A ∈ 𝒫 A := by
  -- 1. mun:subset-self
  have s1 : A ⊆ A := by exact (Parley.Items.Stdlib.Sets.mun_subset_self (X := A))
  -- 2. def:powerset S := A, from 1
  have s2 : A ∈ 𝒫 A := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_powerset (A := A) (S := A))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_powerset (A := A) (S := A))).mpr (by parley_set_side); parley_set_side)
  all_goals exact s2

end Parley.Proofs.Setmm.PowerSets.SetIsAPartOfItself
