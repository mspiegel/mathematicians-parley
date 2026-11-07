module

public import AlgebraTactics
public import SubstTactics
public import Tactics
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Divisibility

/-! Written from corpus/stdlib/divisibility.proof by parley build lean. -/

public section

namespace Parley.Stdlib.Divisibility.CongruentCancel

theorem congruent_cancel (x : ℤ) (y : ℤ) (c : ℤ) (n : ℤ) (hH4 : 0 < n) (hH5 : x * c ≡ y * c [ZMOD n]) (hH6 : (Int.gcd c n : ℤ) = 1) :
    x ≡ y [ZMOD n] := by
  -- 1. def:congruent-mod a := x·c, b := y·c, from H5
  have s1 : n ∣ x * c - y * c := by first | exact ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := n) (a := x * c) (b := y * c))).mp (by parley_side) | exact (((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := n) (a := x * c) (b := y * c))).mp (by parley_side)).symm | simpa using ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := n) (a := x * c) (b := y * c))).mp (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := n) (a := x * c) (b := y * c))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := n) (a := x * c) (b := y * c))).mp (by parley_side); parley_side)
  -- 2. substitute
  have s2 : n ∣ (x - y) * c := by
    have c1 : x * c - y * c = (x - y) * c := by parley_ring
    have row1 : n ∣ (x - y) * c := by parley_subst_at c1 s1
    exact row1
  -- 3. thm:coprime-divides x := x − y, from H6, 2
  have s3 : n ∣ x - y := by exact (Parley.Items.Stdlib.Divisibility.thm_coprime_divides (x := x - y) (c := c) (n := n) (by parley_side) s2 hH6)
  -- 4. def:congruent-mod a := x, b := y, from 3
  have s4 : x ≡ y [ZMOD n] := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := n) (a := x) (b := y))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := n) (a := x) (b := y))).mpr (by parley_side); parley_side)
  all_goals exact s4

end Parley.Stdlib.Divisibility.CongruentCancel
