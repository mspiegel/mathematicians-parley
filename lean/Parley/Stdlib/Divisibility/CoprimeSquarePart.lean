module

public import AlgebraTactics
public import NormTactics
public import Tactics
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Divisibility

/-! Written from corpus/stdlib/divisibility.proof by parley build lean. -/

public section

namespace Parley.Stdlib.Divisibility.CoprimeSquarePart

set_option maxHeartbeats 600000 in
theorem coprime_square_part (s : ℤ) (hH1 : 0 < s) (t : ℤ) (hH2 : 0 < t) (w : ℤ) (hH3 : 0 < w) (hH4 : (Int.gcd s t : ℤ) = 1) (hH5 : w ^ 2 = s * t) :
    s = (Int.gcd s w : ℤ) ^ 2 := by
  -- 1. def:gcd a := s, b := w
  have s1a : 0 < (Int.gcd s w : ℤ) := by exact (Parley.Items.Stdlib.Divisibility.def_gcd_1 (a := s) (by parley_side) (b := w) (by parley_side))
  have s1b : (Int.gcd s w : ℤ) ∣ s := by exact (Parley.Items.Stdlib.Divisibility.def_gcd_2 (a := s) (by parley_side) (b := w) (by parley_side))
  have s1c : (Int.gcd s w : ℤ) ∣ w := by exact (Parley.Items.Stdlib.Divisibility.def_gcd_3 (a := s) (by parley_side) (b := w) (by parley_side))
  have s1d : ∀ e : ℤ, 0 < e → e ∣ s ∧ e ∣ w → e ≤ (Int.gcd s w : ℤ) := by exact (Parley.Items.Stdlib.Divisibility.def_gcd_4 (a := s) (by parley_side) (b := w) (by parley_side))
  -- 2. mun:divides-self n := s
  have s2 : s ∣ s := by exact (Parley.Items.Stdlib.Divisibility.mun_divides_self (n := s))
  -- 3. mun:divides-multiple e := s, a := s, x := s, from 2
  have s3 : s ∣ s * s := by exact (Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := s) (a := s) (x := s) s2)
  -- 4. mun:divides-multiple e := s, a := s, x := w, from 2
  have s4 : s ∣ s * w := by exact (Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := s) (a := s) (x := w) s2)
  -- 5. thm:divides-gcd d := s, a := s·s, b := s·w, from 3, 4
  have s5 : s ∣ (Int.gcd (s * s) (s * w) : ℤ) := by exact (Parley.Items.Stdlib.Divisibility.thm_divides_gcd (d := s) (a := s * s) (b := s * w) s3 s4)
  -- 6. substitute
  have s6 : s ∣ s * (Int.gcd s w : ℤ) := by
    have c1 : (Int.gcd (s * s) (s * w) : ℤ) = s * (Int.gcd s w : ℤ) := by exact (Parley.Items.Stdlib.Divisibility.mun_gcd_scaled (c := s) (by parley_side) (a := s) (b := w))
    have row1 : s ∣ s * (Int.gcd s w : ℤ) := by (have h := Eq.subst (motive := (fun u : ℤ => s ∣ u)) c1 s5; push_cast at h ⊢; all_goals exact_mod_cast h)
    exact row1
  -- 7. substitute
  have s7 : s ∣ (Int.gcd s w : ℤ) * s := by
    have c1 : s * (Int.gcd s w : ℤ) = (Int.gcd s w : ℤ) * s := by parley_ring
    have row1 : s ∣ (Int.gcd s w : ℤ) * s := by (have h := Eq.subst (motive := (fun u : ℤ => s ∣ u)) c1 s6; push_cast at h ⊢; all_goals exact_mod_cast h)
    exact row1
  -- 8. mun:divides-multiple e := s, a := s, x := t, from 2
  have s8 : s ∣ s * t := by exact (Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := s) (a := s) (x := t) s2)
  -- 9. substitute
  have s9 : s ∣ w * w := by
    have c1 : s * t = w * w := by linear_combination (norm := parley_norm) (-1) * hH5
    have row1 : s ∣ w * w := by (have h := Eq.subst (motive := (fun u : ℤ => s ∣ u)) c1 s8; push_cast at h ⊢; all_goals exact_mod_cast h)
    exact row1
  -- 10. substitute
  have s10 : s ∣ w * s := by
    have c1 : s * w = w * s := by parley_ring
    have row1 : s ∣ w * s := by (have h := Eq.subst (motive := (fun u : ℤ => s ∣ u)) c1 s4; push_cast at h ⊢; all_goals exact_mod_cast h)
    exact row1
  -- 11. thm:divides-gcd d := s, a := w·s, b := w·w, from 9, 10
  have s11 : s ∣ (Int.gcd (w * s) (w * w) : ℤ) := by exact (Parley.Items.Stdlib.Divisibility.thm_divides_gcd (d := s) (a := w * s) (b := w * w) s10 s9)
  -- 12. substitute
  have s12 : s ∣ w * (Int.gcd s w : ℤ) := by
    have c1 : (Int.gcd (w * s) (w * w) : ℤ) = w * (Int.gcd s w : ℤ) := by exact (Parley.Items.Stdlib.Divisibility.mun_gcd_scaled (c := w) (by parley_side) (a := s) (b := w))
    have row1 : s ∣ w * (Int.gcd s w : ℤ) := by (have h := Eq.subst (motive := (fun u : ℤ => s ∣ u)) c1 s11; push_cast at h ⊢; all_goals exact_mod_cast h)
    exact row1
  -- 13. substitute
  have s13 : s ∣ (Int.gcd s w : ℤ) * w := by
    have c1 : w * (Int.gcd s w : ℤ) = (Int.gcd s w : ℤ) * w := by parley_ring
    have row1 : s ∣ (Int.gcd s w : ℤ) * w := by (have h := Eq.subst (motive := (fun u : ℤ => s ∣ u)) c1 s12; push_cast at h ⊢; all_goals exact_mod_cast h)
    exact row1
  -- 14. thm:divides-gcd d := s, a := gcd(s, w)·s, b := gcd(s, w)·w, from 7, 13
  have s14 : s ∣ (Int.gcd ((Int.gcd s w : ℤ) * s) ((Int.gcd s w : ℤ) * w) : ℤ) := by exact (Parley.Items.Stdlib.Divisibility.thm_divides_gcd (d := s) (a := (Int.gcd s w : ℤ) * s) (b := (Int.gcd s w : ℤ) * w) s7 s13)
  -- 15. substitute
  have s15 : s ∣ (Int.gcd s w : ℤ) * (Int.gcd s w : ℤ) := by
    have c1 : (Int.gcd ((Int.gcd s w : ℤ) * s) ((Int.gcd s w : ℤ) * w) : ℤ) = (Int.gcd s w : ℤ) * (Int.gcd s w : ℤ) := by exact (Parley.Items.Stdlib.Divisibility.mun_gcd_scaled (c := (Int.gcd s w : ℤ)) (by parley_side) (a := s) (b := w))
    have row1 : s ∣ (Int.gcd s w : ℤ) * (Int.gcd s w : ℤ) := by (have h := Eq.subst (motive := (fun u : ℤ => s ∣ u)) c1 s14; push_cast at h ⊢; all_goals exact_mod_cast h)
    exact row1
  -- 16. substitute
  have s16 : s ∣ (Int.gcd s w : ℤ) ^ 2 := by
    have c1 : (Int.gcd s w : ℤ) * (Int.gcd s w : ℤ) = (Int.gcd s w : ℤ) ^ 2 := by parley_ring
    have row1 : s ∣ (Int.gcd s w : ℤ) ^ 2 := by (have h := Eq.subst (motive := (fun u : ℤ => s ∣ u)) c1 s15; push_cast at h ⊢; all_goals exact_mod_cast h)
    exact row1
  -- 17. mun:divides-square d := gcd(s, w), n := s, from 1
  have s17 : (Int.gcd s w : ℤ) ^ 2 ∣ s ^ 2 := by exact ((Parley.Items.Stdlib.Divisibility.mun_divides_square (d := (Int.gcd s w : ℤ)) (n := s))).mp s1b
  -- 18. mun:divides-square d := gcd(s, w), n := w, from 1
  have s18 : (Int.gcd s w : ℤ) ^ 2 ∣ w ^ 2 := by exact ((Parley.Items.Stdlib.Divisibility.mun_divides_square (d := (Int.gcd s w : ℤ)) (n := w))).mp s1c
  -- 19. substitute w² = s·t (H5) into line 18
  have s19 : (Int.gcd s w : ℤ) ^ 2 ∣ s * t := by (have h := Eq.subst (motive := (fun u : ℤ => (Int.gcd s w : ℤ) ^ 2 ∣ u)) hH5 s18; push_cast at h ⊢; all_goals exact_mod_cast h)
  -- 20. substitute
  have s20 : (Int.gcd s w : ℤ) ^ 2 ∣ s * s := by
    have c1 : s ^ 2 = s * s := by parley_ring
    have row1 : (Int.gcd s w : ℤ) ^ 2 ∣ s * s := by (have h := Eq.subst (motive := (fun u : ℤ => (Int.gcd s w : ℤ) ^ 2 ∣ u)) c1 s17; push_cast at h ⊢; all_goals exact_mod_cast h)
    exact row1
  -- 21. thm:divides-gcd d := gcd(s, w)², a := s·s, b := s·t, from 19, 20
  have s21 : (Int.gcd s w : ℤ) ^ 2 ∣ (Int.gcd (s * s) (s * t) : ℤ) := by exact (Parley.Items.Stdlib.Divisibility.thm_divides_gcd (d := (Int.gcd s w : ℤ) ^ 2) (a := s * s) (b := s * t) s20 s19)
  -- 22. substitute
  have s22 : (Int.gcd s w : ℤ) ^ 2 ∣ s := by
    have c1 : (Int.gcd (s * s) (s * t) : ℤ) = s * (Int.gcd s t : ℤ) := by exact (Parley.Items.Stdlib.Divisibility.mun_gcd_scaled (c := s) (by parley_side) (a := s) (b := t))
    have row1 : (Int.gcd s w : ℤ) ^ 2 ∣ s * (Int.gcd s t : ℤ) := by (have h := Eq.subst (motive := (fun u : ℤ => (Int.gcd s w : ℤ) ^ 2 ∣ u)) c1 s21; push_cast at h ⊢; all_goals exact_mod_cast h)
    have c2 : s * (Int.gcd s t : ℤ) = s := by (have h := congrArg (fun u : ℤ => s * u) hH4; push_cast [mul_one] at h ⊢; all_goals exact_mod_cast h)
    have row2 : (Int.gcd s w : ℤ) ^ 2 ∣ s := by (have h := Eq.subst (motive := (fun u : ℤ => (Int.gcd s w : ℤ) ^ 2 ∣ u)) c2 row1; push_cast at h ⊢; all_goals exact_mod_cast h)
    exact row2
  -- 23. mun:divides-le e := s, m := gcd(s, w)², from 16
  have r335_1 : 0 < (Int.gcd s w : ℤ) ^ 2 := by parley_side
  have s23 : s ≤ (Int.gcd s w : ℤ) ^ 2 := by exact (Parley.Items.Stdlib.Divisibility.mun_divides_le (e := s) (by parley_side) (m := (Int.gcd s w : ℤ) ^ 2) (by parley_side) s16)
  -- 24. mun:divides-le e := gcd(s, w)², m := s, from 22
  have r339_1 : 0 < (Int.gcd s w : ℤ) ^ 2 := by parley_side
  have s24 : (Int.gcd s w : ℤ) ^ 2 ≤ s := by exact (Parley.Items.Stdlib.Divisibility.mun_divides_le (e := (Int.gcd s w : ℤ) ^ 2) (by parley_side) (m := s) (by parley_side) s22)
  -- 25. antisymmetry, from 23, 24
  parley_side

end Parley.Stdlib.Divisibility.CoprimeSquarePart
