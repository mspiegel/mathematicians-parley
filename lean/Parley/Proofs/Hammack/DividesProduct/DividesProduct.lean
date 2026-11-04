module

public import AlgebraTactics
public import SubstTactics
public import Tactics
public import Parley.Items.Stdlib.Divisibility

/-! Written from proofs/hammack/divides-product.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.DividesProduct.DividesProduct

theorem divides_product (a : ℤ) (b : ℤ) (c : ℤ) (d : ℤ) (hH5 : a ∣ b) (hH6 : c ∣ d) :
    a * c ∣ b * d := by
  -- 1. obtain k: def:divides, from H5
  obtain ⟨k, s1⟩ := ((Parley.Items.Stdlib.Divisibility.def_divides (d := a) (n := b))).mp (by parley_side)
  -- 2. obtain m: def:divides d := c, n := d, from H6
  obtain ⟨m, s2⟩ := ((Parley.Items.Stdlib.Divisibility.def_divides (d := c) (n := d))).mp (by parley_side)
  -- 3. calculation
  have s3 : b * d = a * c * (k * m) := by
    calc b * d = a * k * d := by parley_subst s1
      _ = a * k * (c * m) := by parley_subst s2
      _ = a * c * (k * m) := by parley_ring
  -- 4. def:divides d := a·c, n := b·d, from 3
  have s4 : a * c ∣ b * d := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_divides (d := a * c) (n := b * d))).mpr ⟨k * m, by parley_side⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_divides (d := a * c) (n := b * d))).mpr ⟨k * m, by parley_side⟩; parley_side)
  all_goals exact s4

end Parley.Proofs.Hammack.DividesProduct.DividesProduct
