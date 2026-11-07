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

/-! Written from proofs/wiedijk/divisibility-by-three.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.DivisibilityByThree.CongruentTimes

theorem congruent_times (a : ℤ) (b : ℤ) (c : ℤ) (n : ℤ) (hH4 : 0 < n) (hH5 : a ≡ b [ZMOD n]) :
    a * c ≡ b * c [ZMOD n] := by
  -- 1. def:congruent-mod, from H5
  have s1 : n ∣ a - b := by first | exact ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := n) (a := a) (b := b))).mp (by parley_side) | exact (((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := n) (a := a) (b := b))).mp (by parley_side)).symm | simpa using ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := n) (a := a) (b := b))).mp (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := n) (a := a) (b := b))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := n) (a := a) (b := b))).mp (by parley_side); parley_side)
  -- 2. mun:divides-multiple e := n, a := a − b, x := c, from 1
  have s2 : n ∣ (a - b) * c := by exact (Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := n) (a := a - b) (x := c) s1)
  -- 3. substitute
  have s3 : n ∣ a * c - b * c := by
    have c1 : (a - b) * c = a * c - b * c := by parley_ring
    have row1 : n ∣ a * c - b * c := by parley_subst_at c1 s2
    exact row1
  -- 4. def:congruent-mod, from 3
  have s4 : a * c ≡ b * c [ZMOD n] := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := n) (a := a * c) (b := b * c))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := n) (a := a * c) (b := b * c))).mpr (by parley_side); parley_side)
  all_goals exact s4

end Parley.Proofs.Wiedijk.DivisibilityByThree.CongruentTimes
