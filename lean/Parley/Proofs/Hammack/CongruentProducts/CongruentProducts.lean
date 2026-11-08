module

public import AlgebraTactics
public import SubstTactics
public import Tactics
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Divisibility

/-! Written from proofs/hammack/congruent-products.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.CongruentProducts.CongruentProducts

theorem congruent_products (a : ℤ) (b : ℤ) (c : ℤ) (d : ℤ) (n : ℤ) (hH5 : 0 < n) (hH6 : a ≡ b [ZMOD n]) (hH7 : c ≡ d [ZMOD n]) :
    a * c ≡ b * d [ZMOD n] := by
  -- 1. def:congruent-mod, from H6
  have s1 : n ∣ a - b := ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := n) (a := a) (b := b))).mp hH6
  -- 2. def:congruent-mod, from H7
  have s2 : n ∣ c - d := ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := n) (a := c) (b := d))).mp hH7
  -- 3. mun:divides-combination e := n, a := a − b, b := c − d, x := c, y := b, from 1, 2
  have s3 : n ∣ (a - b) * c + (c - d) * b := by exact (Parley.Items.Stdlib.Divisibility.mun_divides_combination (e := n) (a := a - b) (b := c - d) (x := c) (y := b) s1 s2)
  -- 4. substitute
  have s4 : n ∣ a * c - b * d := by
    have c1 : (a - b) * c + (c - d) * b = a * c - b * d := by parley_ring
    have row1 : n ∣ a * c - b * d := by parley_subst_at c1 s3
    exact row1
  -- 5. def:congruent-mod, from 4
  exact ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := n) (a := a * c) (b := b * d))).mpr s4

end Parley.Proofs.Hammack.CongruentProducts.CongruentProducts
