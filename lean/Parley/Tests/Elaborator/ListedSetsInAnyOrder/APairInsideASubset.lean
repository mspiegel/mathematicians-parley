module

public import SetTactics
public import Tactics
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Insert
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Sets

/-! Written from tests/elaborator/listed-sets-in-any-order.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ListedSetsInAnyOrder.APairInsideASubset

theorem a_pair_inside_a_subset {α : Type*} (X : Set α) (u : α) (hH2 : u ∈ X) (w : α) (hH3 : w ∈ X) :
    ({w, u} : Set α) ⊆ X := by
  -- 1. mun:pair-subset a := u, b := w, from H2, H3
  first | exact (Parley.Items.Stdlib.Sets.mun_pair_subset (X := X) (a := u) (b := w) hH2 hH3) | exact ((Parley.Items.Stdlib.Sets.mun_pair_subset (X := X) (a := u) (b := w) hH2 hH3)).symm | simpa using (Parley.Items.Stdlib.Sets.mun_pair_subset (X := X) (a := u) (b := w) hH2 hH3) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_pair_subset (X := X) (a := u) (b := w) hH2 hH3) | (have h := (Parley.Items.Stdlib.Sets.mun_pair_subset (X := X) (a := u) (b := w) hH2 hH3); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Sets.mun_pair_subset (X := X) (a := u) (b := w) hH2 hH3); parley_set_side)

end Parley.Tests.Elaborator.ListedSetsInAnyOrder.APairInsideASubset
