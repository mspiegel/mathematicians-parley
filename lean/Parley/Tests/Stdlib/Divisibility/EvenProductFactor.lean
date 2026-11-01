module

public import Parley.Items.Stdlib.Divisibility
public import Parley.Library

/-! Written from tests/stdlib/divisibility.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Divisibility.EvenProductFactor

theorem even_product_factor (a : ℤ) (b : ℤ) :
    (Even (a * b) ↔ Even a ∨ Even b) := by
  -- 1. mun:divisibility-even-product-factor
  have s1 : Even (a * b) ↔ Even a ∨ Even b := by first | exact (Parley.Items.Stdlib.Divisibility.mun_even_product_factor (a := a) (b := b)) | exact ((Parley.Items.Stdlib.Divisibility.mun_even_product_factor (a := a) (b := b))).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_even_product_factor (a := a) (b := b))
  all_goals parley_side

end Parley.Tests.Stdlib.Divisibility.EvenProductFactor
