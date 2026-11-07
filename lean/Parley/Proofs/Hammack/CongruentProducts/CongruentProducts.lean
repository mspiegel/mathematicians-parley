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
  have s1 : n ∣ a - b := by first | exact ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := n) (a := a) (b := b))).mp (by parley_side) | exact (((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := n) (a := a) (b := b))).mp (by parley_side)).symm | simpa using ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := n) (a := a) (b := b))).mp (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := n) (a := a) (b := b))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := n) (a := a) (b := b))).mp (by parley_side); parley_side)
  -- 2. def:congruent-mod, from H7
  have s2 : n ∣ c - d := by first | exact ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := n) (a := c) (b := d))).mp (by parley_side) | exact (((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := n) (a := c) (b := d))).mp (by parley_side)).symm | simpa using ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := n) (a := c) (b := d))).mp (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := n) (a := c) (b := d))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := n) (a := c) (b := d))).mp (by parley_side); parley_side)
  -- 3. mun:divides-combination e := n, a := a − b, b := c − d, x := c, y := b, from 1, 2
  have s3 : n ∣ (a - b) * c + (c - d) * b := by first | exact (Parley.Items.Stdlib.Divisibility.mun_divides_combination (e := n) (a := a - b) (b := c - d) (x := c) (y := b) s1 s2) | exact ((Parley.Items.Stdlib.Divisibility.mun_divides_combination (e := n) (a := a - b) (b := c - d) (x := c) (y := b) s1 s2)).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_divides_combination (e := n) (a := a - b) (b := c - d) (x := c) (y := b) s1 s2) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_divides_combination (e := n) (a := a - b) (b := c - d) (x := c) (y := b) s1 s2) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_combination (e := n) (a := a - b) (b := c - d) (x := c) (y := b) s1 s2); parley_side)
  -- 4. substitute
  have s4 : n ∣ a * c - b * d := by
    have c1 : (a - b) * c + (c - d) * b = a * c - b * d := by parley_ring
    have row1 : n ∣ a * c - b * d := by parley_subst_at c1 s3
    exact row1
  -- 5. def:congruent-mod, from 4
  have s5 : a * c ≡ b * d [ZMOD n] := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := n) (a := a * c) (b := b * d))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := n) (a := a * c) (b := b * d))).mpr (by parley_side); parley_side)
  all_goals exact s5

end Parley.Proofs.Hammack.CongruentProducts.CongruentProducts
