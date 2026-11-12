module

public import Tactics
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
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
  have r45_1 : 0 < N := by linarith only [hH2]
  exact ((Parley.Items.Stdlib.Divisibility.mun_mod_remainder (a := A) (m := N) hH2 (r := (0 : ℤ)) (by norm_num) r45_1)).mpr (by simpa only [add_zero] using hH3)

end Parley.Tests.Elaborator.IdentityLeftOut.ACitedExistentialWithoutItsZero
