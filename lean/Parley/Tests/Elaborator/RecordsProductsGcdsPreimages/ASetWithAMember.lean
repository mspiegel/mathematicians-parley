module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Sets

/-! Written from tests/elaborator/records-products-gcds-preimages.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RecordsProductsGcdsPreimages.ASetWithAMember

theorem a_set_with_a_member (A : Set ℂ) (hH2 : (3 : ℂ) ∈ A) :
    ¬ A = ∅ := by
  -- 1. mun:member-nonempty a := 3, Y := A, from H2
  exact (Parley.Items.Stdlib.Sets.mun_member_nonempty (Y := A) (a := (3 : ℂ)) hH2)

end Parley.Tests.Elaborator.RecordsProductsGcdsPreimages.ASetWithAMember
