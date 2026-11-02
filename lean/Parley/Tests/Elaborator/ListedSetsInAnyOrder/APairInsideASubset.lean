module

public import Tactics
public import Parley.Items.Stdlib.Sets

/-! Written from tests/elaborator/listed-sets-in-any-order.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ListedSetsInAnyOrder.APairInsideASubset

theorem a_pair_inside_a_subset {α : Type*} (X : Set α) (u : α) (hH2 : u ∈ X) (w : α) (hH3 : w ∈ X) :
    ({w, u} : Set α) ⊆ X := by
  -- 1. mun:pair-subset a := u, b := w, from H2, H3
  have s1 : ({w, u} : Set α) ⊆ X := by first | exact (Parley.Items.Stdlib.Sets.mun_pair_subset (X := X) (a := u) (b := w) (by parley_side) (by parley_side)) | exact ((Parley.Items.Stdlib.Sets.mun_pair_subset (X := X) (a := u) (b := w) (by parley_side) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_pair_subset (X := X) (a := u) (b := w) (by parley_side) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_pair_subset (X := X) (a := u) (b := w) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Sets.mun_pair_subset (X := X) (a := u) (b := w) (by parley_side) (by parley_side)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Sets.mun_pair_subset (X := X) (a := u) (b := w) (by parley_side) (by parley_side)); parley_side)
  all_goals parley_side

end Parley.Tests.Elaborator.ListedSetsInAnyOrder.APairInsideASubset
