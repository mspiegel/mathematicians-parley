module

public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/setmm/power-sets.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.PowerSets.SetIsAPartOfItself

theorem set_is_a_part_of_itself {α : Type*} [Nonempty α] (A : Set α) :
    A ∈ 𝒫 A := by
  -- 1. mun:subset-self
  have s1 : A ⊆ A := by exact (Parley.Items.Stdlib.Sets.mun_subset_self (X := A))
  -- 2. def:powerset S := A, from 1
  exact ((Parley.Items.Stdlib.Sets.def_powerset (A := A) (S := A))).mpr s1

end Parley.Proofs.Setmm.PowerSets.SetIsAPartOfItself
