module

public import NormTactics
public import Tactics
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
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
    have r20_1 : 0 < N := by linarith only [hH3]
    obtain ⟨q, s1⟩ := ((Parley.Items.Stdlib.Divisibility.mun_mod_remainder (a := A - B) (m := N) hH3 (r := (0 : ℤ)) (by norm_num) r20_1)).mp hC1
    -- 2. mun:mod-multiple r := B, m := N
    have s2 : (q * N + B) % N = B % N := by exact (Parley.Items.Stdlib.Divisibility.mun_mod_multiple (r := B) (m := N) hH3 (q := q))
    -- 3. substitute
    have c1 : q * N + B = A := by linear_combination (norm := parley_norm) s1
    have row1 : A % N = B % N := by (have h := Eq.subst (motive := (fun t : ℤ => t % N = B % N)) c1 s2; push_cast at h ⊢; all_goals exact_mod_cast h)
    exact row1
  · skip
    intro hC2
    -- 4. mun:mod-equal-congruent, from C2
    have s4 : A ≡ B [ZMOD N] := by exact (Parley.Items.Stdlib.Divisibility.mun_mod_equal_congruent (x := A) (y := B) (n := N) hH3 hC2)
    -- 5. def:congruent-mod, from 4
    have s5 : N ∣ A - B := by exact ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := N) (a := A) (b := B))).mp s4
    -- 6. obtain k: def:divides d := N, n := A − B, from 5
    obtain ⟨k, s6⟩ := ((Parley.Items.Stdlib.Divisibility.def_divides (d := N) (n := A - B))).mp s5
    -- 7. algebra, from 6
    have s7 : k * N = A - B := by linear_combination (norm := parley_norm) (-1) * s6
    -- 8. exhibit, from 7
    have s8 : ∃ q : ℤ, q * N = A - B := ⟨k, s7⟩
    -- 9. mun:mod-remainder a := A − B, m := N, r := 0, from 8
    have r50_1 : 0 < N := by linarith only [hH3]
    exact ((Parley.Items.Stdlib.Divisibility.mun_mod_remainder (a := A - B) (m := N) hH3 (r := (0 : ℤ)) (by norm_num) r50_1)).mpr (by simpa only [Int.cast_zero, add_zero] using s8)

end Parley.Proofs.Setmm.DifferenceRemainderZero.DifferenceRemainderZero
