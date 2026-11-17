module

public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Sets

/-! Written from corpus/stdlib/sets.proof by parley build lean. -/

public section

namespace Parley.Stdlib.Sets.SubsetAntisymmetric

theorem subset_antisymmetric {α : Type*} [Nonempty α] (X : Set α) (Y : Set α) (hH3 : X ⊆ Y) (hH4 : Y ⊆ X) :
    X = Y := by
  -- 1. def:subset, from H3
  have s1 : ∀ t ∈ X, t ∈ Y := by exact ((Parley.Items.Stdlib.Sets.def_subset (X := X) (Y := Y))).mp hH3
  -- 2. def:subset X := Y, Y := X, from H4
  have s2 : ∀ t ∈ Y, t ∈ X := by exact ((Parley.Items.Stdlib.Sets.def_subset (X := Y) (Y := X))).mp hH4
  -- 3. axi:extensionality, from 1, 2
  exact (Parley.Items.Stdlib.Sets.axi_extensionality (X := X) (Y := Y) s1 s2)

end Parley.Stdlib.Sets.SubsetAntisymmetric
