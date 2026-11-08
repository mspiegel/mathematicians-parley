module

public import SetTactics
public import Tactics
public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Sets

/-! Written from corpus/stdlib/sets.proof by parley build lean. -/

public section

namespace Parley.Stdlib.Sets.SubsetAntisymmetric

theorem subset_antisymmetric {α : Type*} (X : Set α) (Y : Set α) (hH3 : X ⊆ Y) (hH4 : Y ⊆ X) :
    X = Y := by
  -- 1. def:subset, from H3
  have s1 : ∀ t ∈ X, t ∈ Y := ((Parley.Items.Stdlib.Sets.def_subset (X := X) (Y := Y))).mp hH3
  -- 2. def:subset X := Y, Y := X, from H4
  have s2 : ∀ t ∈ Y, t ∈ X := ((Parley.Items.Stdlib.Sets.def_subset (X := Y) (Y := X))).mp hH4
  -- 3. axi:extensionality, from 1, 2
  exact (Parley.Items.Stdlib.Sets.axi_extensionality (X := X) (Y := Y) s1 s2)

end Parley.Stdlib.Sets.SubsetAntisymmetric
