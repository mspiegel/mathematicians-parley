module

public import SetTactics
public import Tactics
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Insert
public import Parley.Items.Stdlib.Sets

/-! Written from tests/elaborator/an-exhibit-at-an-identity-element.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AnExhibitAtAnIdentityElement.AnExhibitAtAnIdentityElement

theorem an_exhibit_at_an_identity_element (b : ℂ) (T : ℂ) (x : ℂ) (hH4 : x = b + T) :
    (∃ r ∈ ({(1 : ℤ), (2 : ℤ), (3 : ℤ)} : Set ℤ), x = b + (r : ℂ) * T) := by
  -- 1. mun:triple-members
  have s1 : (1 : ℤ) ∈ ({(1 : ℤ), (2 : ℤ), (3 : ℤ)} : Set ℤ) := by first | exact (Parley.Items.Stdlib.Sets.mun_triple_members_1 (u := (1 : ℤ)) (v := (2 : ℤ)) (w := (3 : ℤ))) | exact ((Parley.Items.Stdlib.Sets.mun_triple_members_1 (u := (1 : ℤ)) (v := (2 : ℤ)) (w := (3 : ℤ)))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_triple_members_1 (u := (1 : ℤ)) (v := (2 : ℤ)) (w := (3 : ℤ))) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_triple_members_1 (u := (1 : ℤ)) (v := (2 : ℤ)) (w := (3 : ℤ))) | (have h := (Parley.Items.Stdlib.Sets.mun_triple_members_1 (u := (1 : ℤ)) (v := (2 : ℤ)) (w := (3 : ℤ))); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Sets.mun_triple_members_1 (u := (1 : ℤ)) (v := (2 : ℤ)) (w := (3 : ℤ))); parley_set_side)
  -- 2. exhibit, from H4, 1
  have s2 : ∃ r ∈ ({(1 : ℤ), (2 : ℤ), (3 : ℤ)} : Set ℤ), x = b + (r : ℂ) * T := ⟨(1 : ℤ), by parley_set_side, by parley_set_side⟩
  all_goals exact s2

end Parley.Tests.Elaborator.AnExhibitAtAnIdentityElement.AnExhibitAtAnIdentityElement
