module

public import Tactics
public import Parley.Items.Stdlib.Divisibility

/-! Written from tests/stdlib/divisibility.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Divisibility.EvenProduct

theorem even_product (a : ℤ) (hH2 : Even a) (x : ℤ) :
    Even (a * x) := by
  -- 1. mun:divisibility-even-product, from H2
  have s1 : Even (a * x) := by first | exact (Parley.Items.Stdlib.Divisibility.mun_even_product (a := a) (by parley_side) (x := x)) | exact ((Parley.Items.Stdlib.Divisibility.mun_even_product (a := a) (by parley_side) (x := x))).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_even_product (a := a) (by parley_side) (x := x)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_even_product (a := a) (by parley_side) (x := x)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_even_product (a := a) (by parley_side) (x := x)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_even_product (a := a) (by parley_side) (x := x)); parley_side)
  all_goals parley_side

end Parley.Tests.Stdlib.Divisibility.EvenProduct
