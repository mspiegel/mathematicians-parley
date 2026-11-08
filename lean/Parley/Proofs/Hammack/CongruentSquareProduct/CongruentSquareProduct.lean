module

public import AlgebraTactics
public import SubstTactics
public import Tactics
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Divisibility

/-! Written from proofs/hammack/congruent-square-product.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.CongruentSquareProduct.CongruentSquareProduct

theorem congruent_square_product (a : ℤ) (b : ℤ) (n : ℤ) (hH3 : 0 < n) (hH4 : a ≡ b [ZMOD n]) :
    a ^ 2 ≡ a * b [ZMOD n] := by
  -- 1. def:congruent-mod, from H4
  have s1 : n ∣ a - b := ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := n) (a := a) (b := b))).mp hH4
  -- 2. mun:divides-multiple e := n, a := a − b, x := a, from 1
  have s2 : n ∣ (a - b) * a := by exact (Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := n) (a := a - b) (x := a) s1)
  -- 3. substitute
  have s3 : n ∣ a ^ 2 - a * b := by
    have c1 : (a - b) * a = a ^ 2 - a * b := by parley_ring
    have row1 : n ∣ a ^ 2 - a * b := by parley_subst_at c1 s2
    exact row1
  -- 4. def:congruent-mod, from 3
  exact ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := n) (a := a ^ 2) (b := a * b))).mpr s3

end Parley.Proofs.Hammack.CongruentSquareProduct.CongruentSquareProduct
