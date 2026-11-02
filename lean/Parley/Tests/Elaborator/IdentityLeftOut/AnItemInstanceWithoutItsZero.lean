module

public import Tactics
public import Parley.Items.Stdlib.Divisibility

/-! Written from tests/elaborator/identity-left-out.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.IdentityLeftOut.AnItemInstanceWithoutItsZero

theorem an_item_instance_without_its_zero (A : ℤ) (N : ℕ) (hH2 : 0 < N) (hH3 : A % (N : ℤ) = 0) :
    (∃ q : ℤ, q * (N : ℤ) = A) := by
  -- 1. mun:mod-remainder a := A, m := N, r := 0, from H3
  have r10_1 : 0 < (N : ℤ) := by parley_side
  have s1 : ∃ q : ℤ, q * (N : ℤ) = A := by first | exact ((Parley.Items.Stdlib.Divisibility.mun_mod_remainder (a := A) (m := N) (by parley_side) (r := 0) (by parley_side))).mp (by parley_side) | exact (((Parley.Items.Stdlib.Divisibility.mun_mod_remainder (a := A) (m := N) (by parley_side) (r := 0) (by parley_side))).mp (by parley_side)).symm | simpa using ((Parley.Items.Stdlib.Divisibility.mun_mod_remainder (a := A) (m := N) (by parley_side) (r := 0) (by parley_side))).mp (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Divisibility.mun_mod_remainder (a := A) (m := N) (by parley_side) (r := 0) (by parley_side))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Divisibility.mun_mod_remainder (a := A) (m := N) (by parley_side) (r := 0) (by parley_side))).mp (by parley_side); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := ((Parley.Items.Stdlib.Divisibility.mun_mod_remainder (a := A) (m := N) (by parley_side) (r := 0) (by parley_side))).mp (by parley_side); parley_side)
  all_goals parley_side

end Parley.Tests.Elaborator.IdentityLeftOut.AnItemInstanceWithoutItsZero
