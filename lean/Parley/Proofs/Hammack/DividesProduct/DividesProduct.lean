module

public import AlgebraTactics
public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Divisibility

/-! Written from proofs/hammack/divides-product.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.DividesProduct.DividesProduct

theorem divides_product (a : ℤ) (b : ℤ) (c : ℤ) (d : ℤ) (hH5 : a ∣ b) (hH6 : c ∣ d) :
    a * c ∣ b * d := by
  -- 1. obtain k: def:divides, from H5
  obtain ⟨k, s1⟩ := ((Parley.Items.Stdlib.Divisibility.def_divides (d := a) (n := b))).mp hH5
  -- 2. obtain m: def:divides d := c, n := d, from H6
  obtain ⟨m, s2⟩ := ((Parley.Items.Stdlib.Divisibility.def_divides (d := c) (n := d))).mp hH6
  -- 3. calculation
  have s3 : b * d = a * c * (k * m) := by
    calc b * d = a * k * d := by (have h := congrArg (fun t : ℤ => t * d) s1; push_cast at h ⊢; all_goals exact_mod_cast h)
      _ = a * k * (c * m) := by (have h := congrArg (fun t : ℤ => a * k * t) s2; push_cast at h ⊢; all_goals exact_mod_cast h)
      _ = a * c * (k * m) := by parley_ring
  -- 4. def:divides d := a·c, n := b·d, from 3
  exact ((Parley.Items.Stdlib.Divisibility.def_divides (d := a * c) (n := b * d))).mpr ⟨k * m, s3⟩

end Parley.Proofs.Hammack.DividesProduct.DividesProduct
