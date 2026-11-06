module

public import PowerTactics
public import Tactics
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Parley.Items.Stdlib.Divisibility

/-! Written from tests/elaborator/records-products-gcds-preimages.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RecordsProductsGcdsPreimages.AGcdScaledByAnInteger

theorem a_gcd_scaled_by_an_integer (a : ℤ) (b : ℤ) (c : ℤ) :
    (Int.gcd (c * a) (c * b) : ℤ) = abs (c * (Int.gcd a b : ℤ)) := by
  -- 1. mun:gcd-scaled-integer
  have s1 : (Int.gcd (c * a) (c * b) : ℤ) = abs (c * (Int.gcd a b : ℤ)) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Divisibility.mun_gcd_scaled_integer (c := c) (a := a) (b := b)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_gcd_scaled_integer (c := c) (a := a) (b := b)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_gcd_scaled_integer (c := c) (a := a) (b := b)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_gcd_scaled_integer (c := c) (a := a) (b := b)) | exact_mod_cast ((Parley.Items.Stdlib.Divisibility.mun_gcd_scaled_integer (c := c) (a := a) (b := b))).symm | (have h := (Parley.Items.Stdlib.Divisibility.mun_gcd_scaled_integer (c := c) (a := a) (b := b)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_gcd_scaled_integer (c := c) (a := a) (b := b)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_gcd_scaled_integer (c := c) (a := a) (b := b)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_gcd_scaled_integer (c := c) (a := a) (b := b)); parley_side)
  all_goals exact s1

end Parley.Tests.Elaborator.RecordsProductsGcdsPreimages.AGcdScaledByAnInteger
