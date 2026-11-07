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

/-! Written from proofs/hammack/congruent-cubes.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.CongruentCubes.CongruentCubes

theorem congruent_cubes (a : ℤ) (b : ℤ) (n : ℤ) (hH3 : 0 < n) (hH4 : a ≡ b [ZMOD n]) :
    a ^ 3 ≡ b ^ 3 [ZMOD n] := by
  -- 1. def:congruent-mod, from H4
  have s1 : n ∣ a - b := by first | exact ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := n) (a := a) (b := b))).mp (by parley_side) | exact (((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := n) (a := a) (b := b))).mp (by parley_side)).symm | simpa using ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := n) (a := a) (b := b))).mp (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := n) (a := a) (b := b))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := n) (a := a) (b := b))).mp (by parley_side); parley_side)
  -- 2. mun:divides-multiple e := n, a := a − b, x := a² + a·b + b², from 1
  have s2 : n ∣ (a - b) * (a ^ 2 + a * b + b ^ 2) := by exact (Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := n) (a := a - b) (x := a ^ 2 + a * b + b ^ 2) s1)
  -- 3. substitute
  have s3 : n ∣ a ^ 3 - b ^ 3 := by
    have c1 : (a - b) * (a ^ 2 + a * b + b ^ 2) = a ^ 3 - b ^ 3 := by parley_ring
    have row1 : n ∣ a ^ 3 - b ^ 3 := by parley_subst_at c1 s2
    exact row1
  -- 4. def:congruent-mod, from 3
  have s4 : a ^ 3 ≡ b ^ 3 [ZMOD n] := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := n) (a := a ^ 3) (b := b ^ 3))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := n) (a := a ^ 3) (b := b ^ 3))).mpr (by parley_side); parley_side)
  all_goals exact s4

end Parley.Proofs.Hammack.CongruentCubes.CongruentCubes
