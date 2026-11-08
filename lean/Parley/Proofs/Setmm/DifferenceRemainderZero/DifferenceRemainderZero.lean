module

public import NormTactics
public import OrderTactics
public import SubstTactics
public import Tactics
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Divisibility

/-! Written from proofs/setmm/difference-remainder-zero.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.DifferenceRemainderZero.DifferenceRemainderZero

theorem difference_remainder_zero (A : ℤ) (B : ℤ) (N : ℤ) (hH3 : 0 < N) :
    ((A - B) % N = 0 ↔ A % N = B % N) := by
  -- the theorem. both directions
  constructor
  · skip
    intro hC1
    -- 1. obtain q: mun:mod-remainder a := A − B, m := N, r := 0, from C1
    have r20_1 : 0 < N := by parley_order
    obtain ⟨q, s1⟩ := ((Parley.Items.Stdlib.Divisibility.mun_mod_remainder (a := A - B) (m := N) (by parley_side) (r := (0 : ℤ)) (by parley_side) r20_1)).mp hC1
    -- 2. mun:mod-multiple r := B, m := N
    have s2 : (q * N + B) % N = B % N := by exact (Parley.Items.Stdlib.Divisibility.mun_mod_multiple (r := B) (m := N) (by parley_side) (q := q))
    -- 3. substitute
    have c1 : q * N + B = A := by linear_combination (norm := parley_norm) s1
    have row1 : A % N = B % N := by parley_subst_at c1 s2
    exact row1
  · skip
    intro hC2
    -- 4. mun:mod-equal-congruent, from C2
    have s4 : A ≡ B [ZMOD N] := by exact (Parley.Items.Stdlib.Divisibility.mun_mod_equal_congruent (x := A) (y := B) (n := N) (by parley_side) hC2)
    -- 5. def:congruent-mod, from 4
    have s5 : N ∣ A - B := ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := N) (a := A) (b := B))).mp s4
    -- 6. obtain k: def:divides d := N, n := A − B, from 5
    obtain ⟨k, s6⟩ := ((Parley.Items.Stdlib.Divisibility.def_divides (d := N) (n := A - B))).mp s5
    -- 7. algebra, from 6
    have s7 : k * N = A - B := by linear_combination (norm := parley_norm) (-1) * s6
    -- 8. exhibit, from 7
    have s8 : ∃ q : ℤ, q * N = A - B := ⟨k, s7⟩
    -- 9. mun:mod-remainder a := A − B, m := N, r := 0, from 8
    have r50_1 : 0 < N := by parley_order
    first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.mun_mod_remainder (a := A - B) (m := N) (by parley_side) (r := (0 : ℤ)) (by parley_side) r50_1)).mpr (by simpa only [add_zero] using s8) | (have h := ((Parley.Items.Stdlib.Divisibility.mun_mod_remainder (a := A - B) (m := N) (by parley_side) (r := (0 : ℤ)) (by parley_side) r50_1)).mpr (by simpa only [add_zero] using s8); parley_side)

end Parley.Proofs.Setmm.DifferenceRemainderZero.DifferenceRemainderZero
