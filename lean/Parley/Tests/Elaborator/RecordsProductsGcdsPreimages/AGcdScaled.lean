module

public import PowerTactics
public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Parley.Items.Stdlib.Divisibility

/-! Written from tests/elaborator/records-products-gcds-preimages.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RecordsProductsGcdsPreimages.AGcdScaled

theorem a_gcd_scaled (a : ℤ) (b : ℤ) :
    (Int.gcd (3 * a) (3 * b) : ℤ) = 3 * (Int.gcd a b : ℤ) := by
  -- 1. mun:gcd-scaled c := 3
  have s1 : (Int.gcd (3 * a) (3 * b) : ℤ) = 3 * (Int.gcd a b : ℤ) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Divisibility.mun_gcd_scaled (c := (3 : ℤ)) (by parley_side) (a := a) (b := b)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_gcd_scaled (c := (3 : ℤ)) (by parley_side) (a := a) (b := b)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_gcd_scaled (c := (3 : ℤ)) (by parley_side) (a := a) (b := b)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_gcd_scaled (c := (3 : ℤ)) (by parley_side) (a := a) (b := b)) | exact_mod_cast ((Parley.Items.Stdlib.Divisibility.mun_gcd_scaled (c := (3 : ℤ)) (by parley_side) (a := a) (b := b))).symm | (have h := (Parley.Items.Stdlib.Divisibility.mun_gcd_scaled (c := (3 : ℤ)) (by parley_side) (a := a) (b := b)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_gcd_scaled (c := (3 : ℤ)) (by parley_side) (a := a) (b := b)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_gcd_scaled (c := (3 : ℤ)) (by parley_side) (a := a) (b := b)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_gcd_scaled (c := (3 : ℤ)) (by parley_side) (a := a) (b := b)); parley_side)
  all_goals exact s1

end Parley.Tests.Elaborator.RecordsProductsGcdsPreimages.AGcdScaled
