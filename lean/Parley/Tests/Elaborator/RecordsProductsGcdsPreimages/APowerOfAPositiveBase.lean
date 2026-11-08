module

public import ArithTactics
public import PowerTactics
public import Tactics
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Rat.Init
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Positivity.Core
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/elaborator/records-products-gcds-preimages.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RecordsProductsGcdsPreimages.APowerOfAPositiveBase

theorem a_power_of_a_positive_base (n : ℤ) (hH1 : 0 < n) :
    (2 ^ n.toNat : ℤ) > 0 := by
  -- 1. mun:power-positive a := 2, m := n
  have r58_1 : (2 : ℤ) > 0 := by parley_arith
  first | (have h := (Parley.Items.Stdlib.Numbers.mun_power_positive (a := (2 : ℚ)) (m := n) (by parley_side)); simp (disch := first | omega | positivity | nlinarith) only [parley_zpow_toNat] at h ⊢; first | exact_mod_cast h | linarith) | linarith [(Parley.Items.Stdlib.Numbers.mun_power_positive (a := (2 : ℚ)) (m := n) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_power_positive (a := (2 : ℚ)) (m := n) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_power_positive (a := (2 : ℚ)) (m := n) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_power_positive (a := (2 : ℚ)) (m := n) (by parley_side)); parley_side)

end Parley.Tests.Elaborator.RecordsProductsGcdsPreimages.APowerOfAPositiveBase
