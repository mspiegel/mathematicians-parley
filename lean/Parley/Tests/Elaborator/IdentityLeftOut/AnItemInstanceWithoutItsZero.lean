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

namespace Parley.Tests.Elaborator.IdentityLeftOut.AnItemInstanceWithoutItsZero

theorem an_item_instance_without_its_zero (A : ℤ) (N : ℤ) (hH2 : 0 < N) (hH3 : A % N = 0) :
    (∃ q : ℤ, q * N = A) := by
  -- 1. mun:mod-remainder a := A, m := N, r := 0, from H3
  have r10_1 : 0 < N := by parley_order
  simpa only [add_zero] using ((Parley.Items.Stdlib.Divisibility.mun_mod_remainder (a := A) (m := N) hH2 (r := (0 : ℤ)) (by parley_side) r10_1)).mp hH3

end Parley.Tests.Elaborator.IdentityLeftOut.AnItemInstanceWithoutItsZero
