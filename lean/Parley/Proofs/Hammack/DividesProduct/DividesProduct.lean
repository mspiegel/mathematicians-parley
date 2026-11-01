module

public import Parley.Items.Stdlib.Divisibility
public import Parley.Library

/-! Written from proofs/hammack/divides-product.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.DividesProduct.DividesProduct

theorem divides_product (a : ℤ) (b : ℤ) (c : ℤ) (d : ℤ) (H5 : a ∣ b) (H6 : c ∣ d) :
    a * c ∣ b * d := by
  -- 1. obtain k: def:divides, from H5
  obtain ⟨k, s1⟩ := ((Parley.Items.Stdlib.Divisibility.def_divides (d := a) (n := b))).mp (by parley_side)
  -- 2. obtain m: def:divides d := c, n := d, from H6
  obtain ⟨m, s2⟩ := ((Parley.Items.Stdlib.Divisibility.def_divides (d := c) (n := d))).mp (by parley_side)
  -- 3. calculation
  have s3 : b * d = a * c * (k * m) := by
    calc b * d = a * k * d := by parley_subst s1
      _ = a * k * (c * m) := by parley_subst s2
      _ = a * c * (k * m) := by ring
  -- 4. def:divides d := a·c, n := b·d, from 3
  have s4 : a * c ∣ b * d := ((Parley.Items.Stdlib.Divisibility.def_divides (d := a * c) (n := b * d))).mpr ⟨k * m, by parley_side⟩
  parley_side

end Parley.Proofs.Hammack.DividesProduct.DividesProduct
