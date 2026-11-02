module

public import LeanBridges
public import Parley.Items.Stdlib.Divisibility

/-! Written from tests/elaborator/identity-left-out.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.IdentityLeftOut.ACitedExistentialWithoutItsZero

theorem a_cited_existential_without_its_zero (A : ℤ) (N : ℕ) (hH2 : 0 < N) (hH3 : ∃ q : ℤ, q * (N : ℤ) = A) :
    A % (N : ℤ) = 0 := by
  -- 1. mun:mod-remainder a := A, m := N, r := 0, from H3
  have r45_1 : 0 < (N : ℤ) := by parley_side
  have s1 : A % (N : ℤ) = 0 := ((Parley.Items.Stdlib.Divisibility.mun_mod_remainder (a := A) (m := N) (by parley_side) (r := 0) (by parley_side))).mpr (by parley_side)
  all_goals parley_side

end Parley.Tests.Elaborator.IdentityLeftOut.ACitedExistentialWithoutItsZero
