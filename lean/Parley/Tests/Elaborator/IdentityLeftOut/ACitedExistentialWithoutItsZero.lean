module

public import OrderTactics
public import Tactics
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Divisibility

/-! Written from tests/elaborator/identity-left-out.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.IdentityLeftOut.ACitedExistentialWithoutItsZero

theorem a_cited_existential_without_its_zero (A : ℤ) (N : ℤ) (hH2 : 0 < N) (hH3 : ∃ q : ℤ, q * N = A) :
    A % N = 0 := by
  -- 1. mun:mod-remainder a := A, m := N, r := 0, from H3
  have r45_1 : 0 < N := by parley_order
  first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.mun_mod_remainder (a := A) (m := N) (by parley_side) (r := (0 : ℤ)) (by parley_side) r45_1)).mpr (by simpa only [add_zero] using hH3) | (have h := ((Parley.Items.Stdlib.Divisibility.mun_mod_remainder (a := A) (m := N) (by parley_side) (r := (0 : ℤ)) (by parley_side) r45_1)).mpr (by simpa only [add_zero] using hH3); parley_side)

end Parley.Tests.Elaborator.IdentityLeftOut.ACitedExistentialWithoutItsZero
