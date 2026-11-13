module

public import SetTactics
public import Tactics
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Sets

/-! Written from tests/elaborator/an-exhibit-at-an-identity-element.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AnExhibitAtAnIdentityElement.AnExhibitAtAnIdentityElement

theorem an_exhibit_at_an_identity_element (b : ℂ) (T : ℂ) (x : ℂ) (hH4 : x = b + T) :
    (∃ r ∈ ({(1 : ℤ), (2 : ℤ), (3 : ℤ)} : Set ℤ), x = b + (r : ℂ) * T) := by
  -- 1. mun:triple-members
  have s1 : (1 : ℤ) ∈ ({(1 : ℤ), (2 : ℤ), (3 : ℤ)} : Set ℤ) := by exact (Parley.Items.Stdlib.Sets.mun_triple_members_1 (u := (1 : ℤ)) (v := (2 : ℤ)) (w := (3 : ℤ)))
  -- 2. exhibit, from H4, 1
  exact ⟨(1 : ℤ), s1, by simpa only [one_mul, Int.cast_one] using hH4⟩

end Parley.Tests.Elaborator.AnExhibitAtAnIdentityElement.AnExhibitAtAnIdentityElement
