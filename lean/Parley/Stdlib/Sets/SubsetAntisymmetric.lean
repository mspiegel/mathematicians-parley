module

public import SetTactics
public import Tactics
public import Parley.Items.Stdlib.Sets

/-! Written from corpus/stdlib/sets.proof by parley build lean. -/

public section

namespace Parley.Stdlib.Sets.SubsetAntisymmetric

theorem subset_antisymmetric {α : Type*} (X : Set α) (Y : Set α) (hH3 : X ⊆ Y) (hH4 : Y ⊆ X) :
    X = Y := by
  -- 1. def:subset, from H3
  have s1 : ∀ t ∈ X, t ∈ Y := by first | exact ((Parley.Items.Stdlib.Sets.def_subset (X := X) (Y := Y))).mp (by parley_set_side) | exact (((Parley.Items.Stdlib.Sets.def_subset (X := X) (Y := Y))).mp (by parley_set_side)).symm | simpa using ((Parley.Items.Stdlib.Sets.def_subset (X := X) (Y := Y))).mp (by parley_set_side) | exact_mod_cast ((Parley.Items.Stdlib.Sets.def_subset (X := X) (Y := Y))).mp (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := X) (Y := Y))).mp (by parley_set_side); parley_set_side)
  -- 2. def:subset X := Y, Y := X, from H4
  have s2 : ∀ t ∈ Y, t ∈ X := by first | exact ((Parley.Items.Stdlib.Sets.def_subset (X := Y) (Y := X))).mp (by parley_set_side) | exact (((Parley.Items.Stdlib.Sets.def_subset (X := Y) (Y := X))).mp (by parley_set_side)).symm | simpa using ((Parley.Items.Stdlib.Sets.def_subset (X := Y) (Y := X))).mp (by parley_set_side) | exact_mod_cast ((Parley.Items.Stdlib.Sets.def_subset (X := Y) (Y := X))).mp (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := Y) (Y := X))).mp (by parley_set_side); parley_set_side)
  -- 3. axi:extensionality, from 1, 2
  have s3 : X = Y := by first | exact (Parley.Items.Stdlib.Sets.axi_extensionality (X := X) (Y := Y) s1 s2) | exact ((Parley.Items.Stdlib.Sets.axi_extensionality (X := X) (Y := Y) s1 s2)).symm | simpa using (Parley.Items.Stdlib.Sets.axi_extensionality (X := X) (Y := Y) s1 s2) | exact_mod_cast (Parley.Items.Stdlib.Sets.axi_extensionality (X := X) (Y := Y) s1 s2) | (have h := (Parley.Items.Stdlib.Sets.axi_extensionality (X := X) (Y := Y) s1 s2); parley_set_side)
  all_goals exact s3

end Parley.Stdlib.Sets.SubsetAntisymmetric
