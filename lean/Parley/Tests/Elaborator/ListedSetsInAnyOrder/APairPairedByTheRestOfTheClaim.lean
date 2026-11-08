module

public import SetTactics
public import Tactics
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Insert
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Sets

/-! Written from tests/elaborator/listed-sets-in-any-order.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ListedSetsInAnyOrder.APairPairedByTheRestOfTheClaim

theorem a_pair_paired_by_the_rest_of_the_claim {α : Type*} (x : α) (v : α) (w : α) :
    (x ∈ ({v, w} : Set α) ↔ x = w ∨ x = v) := by
  -- 1. def:pair
  first | exact (Parley.Items.Stdlib.Sets.def_pair (u := w) (w := v) (x := x)) | exact ((Parley.Items.Stdlib.Sets.def_pair (u := w) (w := v) (x := x))).symm | simpa using (Parley.Items.Stdlib.Sets.def_pair (u := w) (w := v) (x := x)) | exact_mod_cast (Parley.Items.Stdlib.Sets.def_pair (u := w) (w := v) (x := x)) | (have h := (Parley.Items.Stdlib.Sets.def_pair (u := w) (w := v) (x := x)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Sets.def_pair (u := w) (w := v) (x := x)); parley_set_side)

end Parley.Tests.Elaborator.ListedSetsInAnyOrder.APairPairedByTheRestOfTheClaim
