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
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Divisibility

/-! Written from proofs/hammack/square-congruent-one-mod-five.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.SquareCongruentOneModFive.SquareCongruentOneModFive

theorem square_congruent_one_mod_five (a : ℤ) (hH2 : a ≡ (1 : ℤ) [ZMOD (5 : ℤ)]) :
    a ^ 2 ≡ (1 : ℤ) [ZMOD (5 : ℤ)] := by
  -- 1. def:congruent-mod, from H2
  have s1 : (5 : ℤ) ∣ a - 1 := ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := (5 : ℤ)) (a := a) (b := (1 : ℤ)))).mp hH2
  -- 2. mun:divides-multiple e := 5, a := a − 1, x := a + 1, from 1
  have s2 : (5 : ℤ) ∣ (a - 1) * (a + 1) := by exact (Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := (5 : ℤ)) (a := a - 1) (x := a + 1) s1)
  -- 3. substitute
  have s3 : (5 : ℤ) ∣ a ^ 2 - 1 := by
    have c1 : (a - 1) * (a + 1) = a ^ 2 - 1 := by parley_ring
    have row1 : (5 : ℤ) ∣ a ^ 2 - 1 := by parley_subst_at c1 s2
    exact row1
  -- 4. def:congruent-mod, from 3
  first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := (5 : ℤ)) (a := a ^ 2) (b := (1 : ℤ)))).mpr s3 | (have h := ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := (5 : ℤ)) (a := a ^ 2) (b := (1 : ℤ)))).mpr s3; parley_side)

end Parley.Proofs.Hammack.SquareCongruentOneModFive.SquareCongruentOneModFive
