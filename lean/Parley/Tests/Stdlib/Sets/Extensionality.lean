module

public import SetTactics
public import Tactics
public import Parley.Items.Stdlib.Sets

/-! Written from tests/stdlib/sets.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Sets.Extensionality

theorem extensionality {α : Type*} (A : Set α) (B : Set α) (hH3 : ∀ x ∈ A, x ∈ B) (hH4 : ∀ x ∈ B, x ∈ A) :
    A = B := by
  -- 1. axi:sets-extensionality X := A, Y := B, from H3, H4
  have s1 : A = B := by first | exact (Parley.Items.Stdlib.Sets.axi_extensionality (X := A) (Y := B) (by parley_set_side) (by parley_set_side)) | exact ((Parley.Items.Stdlib.Sets.axi_extensionality (X := A) (Y := B) (by parley_set_side) (by parley_set_side))).symm | simpa using (Parley.Items.Stdlib.Sets.axi_extensionality (X := A) (Y := B) (by parley_set_side) (by parley_set_side)) | exact_mod_cast (Parley.Items.Stdlib.Sets.axi_extensionality (X := A) (Y := B) (by parley_set_side) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Sets.axi_extensionality (X := A) (Y := B) (by parley_set_side) (by parley_set_side)); parley_set_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Sets.Extensionality
