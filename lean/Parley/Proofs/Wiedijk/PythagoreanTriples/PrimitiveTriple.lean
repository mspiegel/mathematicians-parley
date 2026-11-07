module

public import AlgebraTactics
public import ArithTactics
public import NormTactics
public import OrderTactics
public import PowerTactics
public import SubstTactics
public import Tactics
public import Batteries.Tactic.Init
public import Mathlib.Algebra.Group.Even
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Set
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Reasoning
public import Parley.Proofs.Wiedijk.PythagoreanTriples.LegHypotenuseCoprime
public import Parley.Stdlib.Divisibility.CoprimeSquare

/-! Written from proofs/wiedijk/pythagorean-triples.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.PythagoreanTriples.PrimitiveTriple

set_option maxHeartbeats 1800000 in
theorem primitive_triple (a : ℤ) (hH1 : 0 < a) (b : ℤ) (hH2 : 0 < b) (c : ℤ) (hH3 : 0 < c) (hH4 : a ^ 2 + b ^ 2 = c ^ 2) (hH5 : (Int.gcd a b : ℤ) = 1) (hH6 : Even a) :
    (∃ m : ℤ, 0 < m ∧ (∃ n : ℤ, 0 < n ∧ (((((n < m ∧ (Int.gcd m n : ℤ) = 1) ∧ Odd (m + n)) ∧ a = 2 * m * n) ∧ b = m ^ 2 - n ^ 2) ∧ c = m ^ 2 + n ^ 2))) := by
  -- 1. obtain w: def:even n := a, from H6
  obtain ⟨w, s1⟩ := ((Parley.Items.Stdlib.Divisibility.def_even (n := a))).mp (by parley_side)
  -- 2. inequalities, from H1
  have s2 : 0 < a := by parley_order
  -- 3. substitute a = 2w (line 1) into line 2
  have s3 : 0 < 2 * w := by parley_subst_at s1 s2
  -- 4. mun:pos-int-nat m := w
  have r185_1 : 0 < w := by parley_side
  have s4 : 0 < w := by first | exact (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := w) (by parley_side)) | exact ((Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := w) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := w) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := w) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := w) (by parley_side)); parley_side)
  -- 5. def:divides d := 2, n := a, from 1
  have s5 : (2 : ℤ) ∣ a := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_divides (d := (2 : ℤ)) (n := a))).mpr ⟨w, by parley_side⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (2 : ℤ)) (n := a))).mpr ⟨w, by parley_side⟩; parley_side)
  -- 6. contradiction
  have s6 : Odd b := by
    by_contra hc_hS1
    have hS1 : ¬ Odd b := by parley_suppose hc_hS1
    -- 6.1. mun:even-or-odd n := b
    have s6_1 : Even b ∨ Odd b := by first | exact (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := b)) | exact ((Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := b))).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := b)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := b)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := b)); parley_side)
    -- 6.2. mun:disjunctive-syllogism P := b is even, Q := b is odd, from S1, 6.1
    have s6_2 : Even b := by first | exact (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism (P := Even b) (Q := Odd b) s6_1 hS1) | exact ((Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism (P := Even b) (Q := Odd b) s6_1 hS1)).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism (P := Even b) (Q := Odd b) s6_1 hS1) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism (P := Even b) (Q := Odd b) s6_1 hS1) | (have h := (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism (P := Even b) (Q := Odd b) s6_1 hS1); parley_side)
    -- 6.3. obtain v: def:even n := b, from 6.2
    obtain ⟨v, s6_3⟩ := ((Parley.Items.Stdlib.Divisibility.def_even (n := b))).mp (by parley_side)
    -- 6.4. def:divides d := 2, n := b, from 6.3
    have s6_4 : (2 : ℤ) ∣ b := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_divides (d := (2 : ℤ)) (n := b))).mpr ⟨v, by parley_side⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (2 : ℤ)) (n := b))).mpr ⟨v, by parley_side⟩; parley_side)
    -- 6.5. thm:divides-gcd d := 2, from 5, 6.4
    have s6_5 : (2 : ℤ) ∣ (Int.gcd a b : ℤ) := by first | exact (Parley.Items.Stdlib.Divisibility.thm_divides_gcd (d := (2 : ℤ)) (a := a) (b := b) s5 s6_4) | exact ((Parley.Items.Stdlib.Divisibility.thm_divides_gcd (d := (2 : ℤ)) (a := a) (b := b) s5 s6_4)).symm | simpa using (Parley.Items.Stdlib.Divisibility.thm_divides_gcd (d := (2 : ℤ)) (a := a) (b := b) s5 s6_4) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.thm_divides_gcd (d := (2 : ℤ)) (a := a) (b := b) s5 s6_4) | (have h := (Parley.Items.Stdlib.Divisibility.thm_divides_gcd (d := (2 : ℤ)) (a := a) (b := b) s5 s6_4); parley_side)
    -- 6.6. substitute gcd(a, b) = 1 (H5) into line 6.5
    have s6_6 : (2 : ℤ) ∣ (1 : ℤ) := by first | parley_subst_at hH5 s6_5 | (have e_nat : Int.gcd a b = 1 := by exact_mod_cast hH5; parley_subst_at e_nat s6_5)
    exact absurd s6_6 (by norm_num)
    all_goals parley_side
  -- 7. obtain q: def:odd n := b, from 6
  obtain ⟨q, s7⟩ := ((Parley.Items.Stdlib.Divisibility.def_odd (n := b))).mp (by parley_side)
  -- 8. substitute
  have s8 : (2 * w) ^ 2 + (2 * q + 1) ^ 2 = c ^ 2 := by
    have c1 : a = 2 * w := by parley_subst s1
    have row1 : (2 * w) ^ 2 + b ^ 2 = c ^ 2 := by parley_subst_at c1 hH4
    have c2 : b = 2 * q + 1 := by parley_subst s7
    have row2 : (2 * w) ^ 2 + (2 * q + 1) ^ 2 = c ^ 2 := by parley_subst_at c2 row1
    exact row2
  -- 9. contradiction
  have s9 : Odd c := by
    by_contra hc_hS2
    have hS2 : ¬ Odd c := by parley_suppose hc_hS2
    -- 9.1. mun:even-or-odd n := c
    have s9_1 : Even c ∨ Odd c := by first | exact (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := c)) | exact ((Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := c))).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := c)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := c)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := c)); parley_side)
    -- 9.2. mun:disjunctive-syllogism P := c is even, Q := c is odd, from S2, 9.1
    have s9_2 : Even c := by first | exact (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism (P := Even c) (Q := Odd c) s9_1 hS2) | exact ((Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism (P := Even c) (Q := Odd c) s9_1 hS2)).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism (P := Even c) (Q := Odd c) s9_1 hS2) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism (P := Even c) (Q := Odd c) s9_1 hS2) | (have h := (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism (P := Even c) (Q := Odd c) s9_1 hS2); parley_side)
    -- 9.3. obtain r: def:even n := c, from 9.2
    obtain ⟨r, s9_3⟩ := ((Parley.Items.Stdlib.Divisibility.def_even (n := c))).mp (by parley_side)
    -- 9.4. substitute c = 2r (line 9.3) into line 8
    have s9_4 : (2 * w) ^ 2 + (2 * q + 1) ^ 2 = (2 * r) ^ 2 := by parley_subst_at s9_3 s8
    -- 9.5. algebra, from 9.4
    have s9_5 : 1 = 2 * (2 * r ^ 2 - 2 * w ^ 2 - 2 * q ^ 2 - 2 * q) := by linear_combination (norm := parley_norm) s9_4
    -- 9.6. def:divides d := 2, n := 1, from 9.5
    have s9_6 : (2 : ℤ) ∣ (1 : ℤ) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_divides (d := (2 : ℤ)) (n := (1 : ℤ)))).mpr ⟨2 * r ^ 2 - 2 * w ^ 2 - 2 * q ^ 2 - 2 * q, by parley_side⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (2 : ℤ)) (n := (1 : ℤ)))).mpr ⟨2 * r ^ 2 - 2 * w ^ 2 - 2 * q ^ 2 - 2 * q, by parley_side⟩; parley_side)
    exact absurd s9_6 (by norm_num)
    all_goals parley_side
  -- 10. obtain r: def:odd n := c, from 9
  obtain ⟨r, s10⟩ := ((Parley.Items.Stdlib.Divisibility.def_odd (n := c))).mp (by parley_side)
  -- 11. algebra, from 7, 10
  have s11 : c + b = 2 * (r + q + 1) := by linear_combination (norm := parley_norm) s7 + s10
  -- 12. def:even n := c + b, from 11
  have s12 : Even (c + b) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_even (n := c + b))).mpr ⟨r + q + 1, by parley_side⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_even (n := c + b))).mpr ⟨r + q + 1, by parley_side⟩; parley_side)
  -- 13. obtain s: def:even n := c + b, from 12
  obtain ⟨s, s13⟩ := ((Parley.Items.Stdlib.Divisibility.def_even (n := c + b))).mp (by parley_side)
  -- 14. algebra, from 7, 10
  have s14 : c - b = 2 * (r - q) := by linear_combination (norm := parley_norm) (-1) * s7 + s10
  -- 15. def:even n := c − b, from 14
  have s15 : Even (c - b) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_even (n := c - b))).mpr ⟨r - q, by parley_side⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_even (n := c - b))).mpr ⟨r - q, by parley_side⟩; parley_side)
  -- 16. obtain t: def:even n := c − b, from 15
  obtain ⟨t, s16⟩ := ((Parley.Items.Stdlib.Divisibility.def_even (n := c - b))).mp (by parley_side)
  -- 17. algebra, from 13, 16
  have s17 : c * 2 = (s + t) * 2 := by linear_combination (norm := parley_norm) s13 + s16
  -- 18. mun:multiply-cancel a := c, b := s + t, c := 2, from 17
  have r269_1 : (2 : ℤ) ≠ 0 := by parley_arith
  have s18 : c = s + t := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := c) (b := s + t) (c := (2 : ℤ)) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := c) (b := s + t) (c := (2 : ℤ)) (by parley_side) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := c) (b := s + t) (c := (2 : ℤ)) (by parley_side) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := c) (b := s + t) (c := (2 : ℤ)) (by parley_side) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := c) (b := s + t) (c := (2 : ℤ)) (by parley_side) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := c) (b := s + t) (c := (2 : ℤ)) (by parley_side) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := c) (b := s + t) (c := (2 : ℤ)) (by parley_side) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := c) (b := s + t) (c := (2 : ℤ)) (by parley_side) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := c) (b := s + t) (c := (2 : ℤ)) (by parley_side) (by parley_side)); parley_side)
  -- 19. algebra
  have s19 : (s - t) * 2 = 2 * s - 2 * t := by parley_ring
  -- 20. substitute
  have s20 : (s - t) * 2 = c + b - (c - b) := by
    have c1 : 2 * s = c + b := by parley_subst s13
    have row1 : (s - t) * 2 = c + b - 2 * t := by parley_subst_at c1 s19
    have c2 : 2 * t = c - b := by parley_subst s16
    have row2 : (s - t) * 2 = c + b - (c - b) := by parley_subst_at c2 row1
    exact row2
  -- 21. calculation
  have s21 : b * 2 = (s - t) * 2 := by
    calc b * 2 = c + b - (c - b) := by parley_ring
      _ = (s - t) * 2 := by parley_side
  -- 22. mun:multiply-cancel a := b, b := s − t, c := 2, from 21
  have r287_1 : (2 : ℤ) ≠ 0 := by parley_arith
  have s22 : b = s - t := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := b) (b := s - t) (c := (2 : ℤ)) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := b) (b := s - t) (c := (2 : ℤ)) (by parley_side) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := b) (b := s - t) (c := (2 : ℤ)) (by parley_side) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := b) (b := s - t) (c := (2 : ℤ)) (by parley_side) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := b) (b := s - t) (c := (2 : ℤ)) (by parley_side) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := b) (b := s - t) (c := (2 : ℤ)) (by parley_side) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := b) (b := s - t) (c := (2 : ℤ)) (by parley_side) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := b) (b := s - t) (c := (2 : ℤ)) (by parley_side) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := b) (b := s - t) (c := (2 : ℤ)) (by parley_side) (by parley_side)); parley_side)
  -- 23. mun:square-positive x := a, from H1
  have s23 : a ^ 2 > 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_square_positive (x := a) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_square_positive (x := a) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_square_positive (x := a) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_square_positive (x := a) (by parley_side)); parley_side)
  -- 24. inequalities
  have s24 : b ^ 2 < a ^ 2 + b ^ 2 := by parley_order
  -- 25. transitivity, from 24, H4
  have s25 : b ^ 2 < c ^ 2 := by parley_order
  -- 26. mun:square-less x := b, y := c, from 25
  have r303_1 : b ≥ 0 := by parley_order
  have r303_2 : c ≥ 0 := by parley_order
  have s26 : b < c := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Numbers.mun_square_less (x := b) (y := c) (by parley_side) (by parley_side))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_square_less (x := b) (y := c) (by parley_side) (by parley_side))).mpr (by parley_side); parley_side)
  -- 27. inequalities
  have s27 : 0 < c - b := by parley_order
  -- 28. substitute c − b = 2t (line 16) into line 27
  have s28 : 0 < 2 * t := by parley_subst_at s16 s27
  -- 29. mun:pos-int-nat m := t
  have r316_1 : 0 < t := by parley_side
  have s29 : 0 < t := by first | exact (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := t) (by parley_side)) | exact ((Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := t) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := t) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := t) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := t) (by parley_side)); parley_side)
  -- 30. inequalities, from H2, H3
  have s30 : 0 < c + b := by parley_order
  -- 31. substitute c + b = 2s (line 13) into line 30
  have s31 : 0 < 2 * s := by parley_subst_at s13 s30
  -- 32. mun:pos-int-nat m := s
  have r326_1 : 0 < s := by parley_side
  have s32 : 0 < s := by first | exact (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := s) (by parley_side)) | exact ((Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := s) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := s) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := s) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := s) (by parley_side)); parley_side)
  -- 33. algebra
  have s33 : (c + b) * (c - b) = c ^ 2 - b ^ 2 := by parley_ring
  -- 34. substitute
  have s34 : 2 * s * (2 * t) = c ^ 2 - b ^ 2 := by
    have c1 : c + b = 2 * s := by parley_subst s13
    have row1 : 2 * s * (c - b) = c ^ 2 - b ^ 2 := by parley_subst_at c1 s33
    have c2 : c - b = 2 * t := by parley_subst s16
    have row2 : 2 * s * (2 * t) = c ^ 2 - b ^ 2 := by parley_subst_at c2 row1
    exact row2
  -- 35. calculation
  have s35 : w ^ 2 * 4 = s * t * 4 := by
    calc w ^ 2 * 4 = (2 * w) ^ 2 := by parley_ring
      _ = a ^ 2 := by parley_subst s1
      _ = c ^ 2 - b ^ 2 := by linear_combination (norm := parley_norm) hH4
      _ = 2 * s * (2 * t) := by parley_side
      _ = s * t * 4 := by parley_ring
  -- 36. mun:multiply-cancel a := w², b := s·t, c := 4, from 35
  have r347_1 : (4 : ℤ) ≠ 0 := by parley_arith
  have s36 : w ^ 2 = s * t := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := w ^ 2) (b := s * t) (c := (4 : ℤ)) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := w ^ 2) (b := s * t) (c := (4 : ℤ)) (by parley_side) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := w ^ 2) (b := s * t) (c := (4 : ℤ)) (by parley_side) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := w ^ 2) (b := s * t) (c := (4 : ℤ)) (by parley_side) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := w ^ 2) (b := s * t) (c := (4 : ℤ)) (by parley_side) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := w ^ 2) (b := s * t) (c := (4 : ℤ)) (by parley_side) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := w ^ 2) (b := s * t) (c := (4 : ℤ)) (by parley_side) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := w ^ 2) (b := s * t) (c := (4 : ℤ)) (by parley_side) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := w ^ 2) (b := s * t) (c := (4 : ℤ)) (by parley_side) (by parley_side)); parley_side)
  -- 37. def:gcd a := s, b := t, from 29, 32
  have s37a : 0 < (Int.gcd s t : ℤ) := by first | exact (Parley.Items.Stdlib.Divisibility.def_gcd_1 (a := s) (by parley_side) (b := t) (by parley_side)) | exact ((Parley.Items.Stdlib.Divisibility.def_gcd_1 (a := s) (by parley_side) (b := t) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Divisibility.def_gcd_1 (a := s) (by parley_side) (b := t) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.def_gcd_1 (a := s) (by parley_side) (b := t) (by parley_side)) | (have h := (Parley.Items.Stdlib.Divisibility.def_gcd_1 (a := s) (by parley_side) (b := t) (by parley_side)); parley_side)
  have s37b : (Int.gcd s t : ℤ) ∣ s := by first | exact (Parley.Items.Stdlib.Divisibility.def_gcd_2 (a := s) (by parley_side) (b := t) (by parley_side)) | exact ((Parley.Items.Stdlib.Divisibility.def_gcd_2 (a := s) (by parley_side) (b := t) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Divisibility.def_gcd_2 (a := s) (by parley_side) (b := t) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.def_gcd_2 (a := s) (by parley_side) (b := t) (by parley_side)) | (have h := (Parley.Items.Stdlib.Divisibility.def_gcd_2 (a := s) (by parley_side) (b := t) (by parley_side)); parley_side)
  have s37c : (Int.gcd s t : ℤ) ∣ t := by first | exact (Parley.Items.Stdlib.Divisibility.def_gcd_3 (a := s) (by parley_side) (b := t) (by parley_side)) | exact ((Parley.Items.Stdlib.Divisibility.def_gcd_3 (a := s) (by parley_side) (b := t) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Divisibility.def_gcd_3 (a := s) (by parley_side) (b := t) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.def_gcd_3 (a := s) (by parley_side) (b := t) (by parley_side)) | (have h := (Parley.Items.Stdlib.Divisibility.def_gcd_3 (a := s) (by parley_side) (b := t) (by parley_side)); parley_side)
  -- 38. mun:divides-sum d := gcd(s, t), a := s, b := t, from 37
  have s38 : (Int.gcd s t : ℤ) ∣ s + t := by first | exact (Parley.Items.Stdlib.Divisibility.mun_divides_sum (d := (Int.gcd s t : ℤ)) (a := s) (b := t) s37b s37c) | exact ((Parley.Items.Stdlib.Divisibility.mun_divides_sum (d := (Int.gcd s t : ℤ)) (a := s) (b := t) s37b s37c)).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_divides_sum (d := (Int.gcd s t : ℤ)) (a := s) (b := t) s37b s37c) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_divides_sum (d := (Int.gcd s t : ℤ)) (a := s) (b := t) s37b s37c) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_sum (d := (Int.gcd s t : ℤ)) (a := s) (b := t) s37b s37c); parley_side)
  -- 39. substitute c = s + t (line 18) into line 38
  have s39 : (Int.gcd s t : ℤ) ∣ c := by parley_subst_at s18 s38
  -- 40. mun:divides-difference d := gcd(s, t), a := s, b := t, from 37
  have s40 : (Int.gcd s t : ℤ) ∣ s - t := by first | exact (Parley.Items.Stdlib.Divisibility.mun_divides_difference (d := (Int.gcd s t : ℤ)) (a := s) (b := t) s37b s37c) | exact ((Parley.Items.Stdlib.Divisibility.mun_divides_difference (d := (Int.gcd s t : ℤ)) (a := s) (b := t) s37b s37c)).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_divides_difference (d := (Int.gcd s t : ℤ)) (a := s) (b := t) s37b s37c) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_divides_difference (d := (Int.gcd s t : ℤ)) (a := s) (b := t) s37b s37c) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_difference (d := (Int.gcd s t : ℤ)) (a := s) (b := t) s37b s37c); parley_side)
  -- 41. substitute b = s − t (line 22) into line 40
  have s41 : (Int.gcd s t : ℤ) ∣ b := by parley_subst_at s22 s40
  -- 42. thm:divides-gcd d := gcd(s, t), a := b, b := c, from 39, 41
  have s42 : (Int.gcd s t : ℤ) ∣ (Int.gcd b c : ℤ) := by first | exact (Parley.Items.Stdlib.Divisibility.thm_divides_gcd (d := (Int.gcd s t : ℤ)) (a := b) (b := c) s41 s39) | exact ((Parley.Items.Stdlib.Divisibility.thm_divides_gcd (d := (Int.gcd s t : ℤ)) (a := b) (b := c) s41 s39)).symm | simpa using (Parley.Items.Stdlib.Divisibility.thm_divides_gcd (d := (Int.gcd s t : ℤ)) (a := b) (b := c) s41 s39) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.thm_divides_gcd (d := (Int.gcd s t : ℤ)) (a := b) (b := c) s41 s39) | (have h := (Parley.Items.Stdlib.Divisibility.thm_divides_gcd (d := (Int.gcd s t : ℤ)) (a := b) (b := c) s41 s39); parley_side)
  -- 43. substitute
  have s43 : (Int.gcd s t : ℤ) ∣ (1 : ℤ) := by
    have c1 : (Int.gcd b c : ℤ) = 1 := by first | linear_combination (norm := parley_norm) (Parley.Proofs.Wiedijk.PythagoreanTriples.LegHypotenuseCoprime.leg_hypotenuse_coprime (a := a) (by parley_side) (b := b) (by parley_side) (c := c) (by parley_side) hH4 hH5) | (have h := (Parley.Proofs.Wiedijk.PythagoreanTriples.LegHypotenuseCoprime.leg_hypotenuse_coprime (a := a) (by parley_side) (b := b) (by parley_side) (c := c) (by parley_side) hH4 hH5); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Wiedijk.PythagoreanTriples.LegHypotenuseCoprime.leg_hypotenuse_coprime (a := a) (by parley_side) (b := b) (by parley_side) (c := c) (by parley_side) hH4 hH5); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Proofs.Wiedijk.PythagoreanTriples.LegHypotenuseCoprime.leg_hypotenuse_coprime (a := a) (by parley_side) (b := b) (by parley_side) (c := c) (by parley_side) hH4 hH5) | exact_mod_cast ((Parley.Proofs.Wiedijk.PythagoreanTriples.LegHypotenuseCoprime.leg_hypotenuse_coprime (a := a) (by parley_side) (b := b) (by parley_side) (c := c) (by parley_side) hH4 hH5)).symm | (have h := (Parley.Proofs.Wiedijk.PythagoreanTriples.LegHypotenuseCoprime.leg_hypotenuse_coprime (a := a) (by parley_side) (b := b) (by parley_side) (c := c) (by parley_side) hH4 hH5); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Wiedijk.PythagoreanTriples.LegHypotenuseCoprime.leg_hypotenuse_coprime (a := a) (by parley_side) (b := b) (by parley_side) (c := c) (by parley_side) hH4 hH5); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Wiedijk.PythagoreanTriples.LegHypotenuseCoprime.leg_hypotenuse_coprime (a := a) (by parley_side) (b := b) (by parley_side) (c := c) (by parley_side) hH4 hH5); parley_int_power h) | (have h := (Parley.Proofs.Wiedijk.PythagoreanTriples.LegHypotenuseCoprime.leg_hypotenuse_coprime (a := a) (by parley_side) (b := b) (by parley_side) (c := c) (by parley_side) hH4 hH5); parley_side)
    have row1 : (Int.gcd s t : ℤ) ∣ (1 : ℤ) := by parley_subst_at c1 s42
    exact row1
  -- 44. mun:divides-one d := gcd(s, t), from 37, 43
  have s44 : (Int.gcd s t : ℤ) = 1 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := (Int.gcd s t : ℤ)) (by parley_side) s43) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := (Int.gcd s t : ℤ)) (by parley_side) s43); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := (Int.gcd s t : ℤ)) (by parley_side) s43); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := (Int.gcd s t : ℤ)) (by parley_side) s43) | exact_mod_cast ((Parley.Items.Stdlib.Divisibility.mun_divides_one (d := (Int.gcd s t : ℤ)) (by parley_side) s43)).symm | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := (Int.gcd s t : ℤ)) (by parley_side) s43); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := (Int.gcd s t : ℤ)) (by parley_side) s43); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := (Int.gcd s t : ℤ)) (by parley_side) s43); parley_int_power h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := (Int.gcd s t : ℤ)) (by parley_side) s43); parley_side)
  -- 45. thm:coprime-square, from 4, 29, 32, 36, 44
  have s45a : s = (Int.gcd s w : ℤ) ^ 2 := by first | linear_combination (norm := parley_norm) (Parley.Stdlib.Divisibility.CoprimeSquare.coprime_square (s := s) (by parley_side) (t := t) (by parley_side) (w := w) (by parley_side) s44 s36).1 | (have h := (Parley.Stdlib.Divisibility.CoprimeSquare.coprime_square (s := s) (by parley_side) (t := t) (by parley_side) (w := w) (by parley_side) s44 s36).1; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Stdlib.Divisibility.CoprimeSquare.coprime_square (s := s) (by parley_side) (t := t) (by parley_side) (w := w) (by parley_side) s44 s36).1; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Stdlib.Divisibility.CoprimeSquare.coprime_square (s := s) (by parley_side) (t := t) (by parley_side) (w := w) (by parley_side) s44 s36).1 | exact_mod_cast ((Parley.Stdlib.Divisibility.CoprimeSquare.coprime_square (s := s) (by parley_side) (t := t) (by parley_side) (w := w) (by parley_side) s44 s36).1).symm | (have h := (Parley.Stdlib.Divisibility.CoprimeSquare.coprime_square (s := s) (by parley_side) (t := t) (by parley_side) (w := w) (by parley_side) s44 s36).1; rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Stdlib.Divisibility.CoprimeSquare.coprime_square (s := s) (by parley_side) (t := t) (by parley_side) (w := w) (by parley_side) s44 s36).1; qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Stdlib.Divisibility.CoprimeSquare.coprime_square (s := s) (by parley_side) (t := t) (by parley_side) (w := w) (by parley_side) s44 s36).1; parley_int_power h) | (have h := (Parley.Stdlib.Divisibility.CoprimeSquare.coprime_square (s := s) (by parley_side) (t := t) (by parley_side) (w := w) (by parley_side) s44 s36).1; parley_side)
  have s45b : t = (Int.gcd t w : ℤ) ^ 2 := by first | linear_combination (norm := parley_norm) (Parley.Stdlib.Divisibility.CoprimeSquare.coprime_square (s := s) (by parley_side) (t := t) (by parley_side) (w := w) (by parley_side) s44 s36).2 | (have h := (Parley.Stdlib.Divisibility.CoprimeSquare.coprime_square (s := s) (by parley_side) (t := t) (by parley_side) (w := w) (by parley_side) s44 s36).2; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Stdlib.Divisibility.CoprimeSquare.coprime_square (s := s) (by parley_side) (t := t) (by parley_side) (w := w) (by parley_side) s44 s36).2; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Stdlib.Divisibility.CoprimeSquare.coprime_square (s := s) (by parley_side) (t := t) (by parley_side) (w := w) (by parley_side) s44 s36).2 | exact_mod_cast ((Parley.Stdlib.Divisibility.CoprimeSquare.coprime_square (s := s) (by parley_side) (t := t) (by parley_side) (w := w) (by parley_side) s44 s36).2).symm | (have h := (Parley.Stdlib.Divisibility.CoprimeSquare.coprime_square (s := s) (by parley_side) (t := t) (by parley_side) (w := w) (by parley_side) s44 s36).2; rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Stdlib.Divisibility.CoprimeSquare.coprime_square (s := s) (by parley_side) (t := t) (by parley_side) (w := w) (by parley_side) s44 s36).2; qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Stdlib.Divisibility.CoprimeSquare.coprime_square (s := s) (by parley_side) (t := t) (by parley_side) (w := w) (by parley_side) s44 s36).2; parley_int_power h) | (have h := (Parley.Stdlib.Divisibility.CoprimeSquare.coprime_square (s := s) (by parley_side) (t := t) (by parley_side) (w := w) (by parley_side) s44 s36).2; parley_side)
  have hD1_kind : 0 < (Int.gcd s w : ℤ) := by first | exact (Parley.Items.Stdlib.Divisibility.def_gcd_1 (a := s) (by parley_side) (b := w) (by parley_side)) | exact ((Parley.Items.Stdlib.Divisibility.def_gcd_1 (a := s) (by parley_side) (b := w) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Divisibility.def_gcd_1 (a := s) (by parley_side) (b := w) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.def_gcd_1 (a := s) (by parley_side) (b := w) (by parley_side)) | (have h := (Parley.Items.Stdlib.Divisibility.def_gcd_1 (a := s) (by parley_side) (b := w) (by parley_side)); parley_side)
  set m : ℤ := (Int.gcd s w : ℤ) with hD1
  have hD1_pos := hD1_kind
  -- 46. calculation
  have s46 : s = m ^ 2 := by
    calc s = (Int.gcd s w : ℤ) ^ 2 := by parley_side
      _ = m ^ 2 := by first | (simp (disch := omega) only [hD1]; done) | (simp (disch := omega) only [hD1]; push_cast; norm_num; done) | parley_side
  have hD2_kind : 0 < (Int.gcd t w : ℤ) := by first | exact (Parley.Items.Stdlib.Divisibility.def_gcd_1 (a := t) (by parley_side) (b := w) (by parley_side)) | exact ((Parley.Items.Stdlib.Divisibility.def_gcd_1 (a := t) (by parley_side) (b := w) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Divisibility.def_gcd_1 (a := t) (by parley_side) (b := w) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.def_gcd_1 (a := t) (by parley_side) (b := w) (by parley_side)) | (have h := (Parley.Items.Stdlib.Divisibility.def_gcd_1 (a := t) (by parley_side) (b := w) (by parley_side)); parley_side)
  set n : ℤ := (Int.gcd t w : ℤ) with hD2
  have hD2_pos := hD2_kind
  -- 47. calculation
  have s47 : t = n ^ 2 := by
    calc t = (Int.gcd t w : ℤ) ^ 2 := by parley_side
      _ = n ^ 2 := by first | (simp (disch := omega) only [hD2]; done) | (simp (disch := omega) only [hD2]; push_cast; norm_num; done) | parley_side
  -- 48. substitute
  have s48 : w ^ 2 = m ^ 2 * n ^ 2 := by
    have c1 : s = m ^ 2 := by parley_subst s46
    have row1 : w ^ 2 = m ^ 2 * t := by parley_subst_at c1 s36
    have c2 : t = n ^ 2 := by parley_subst s47
    have row2 : w ^ 2 = m ^ 2 * n ^ 2 := by parley_subst_at c2 row1
    exact row2
  -- 49. membership
  have s49 : 0 < m * n := by parley_side
  -- 50. algebra, from 48
  have s50 : w ^ 2 = (m * n) ^ 2 := by linear_combination (norm := parley_norm) s48
  -- 51. mun:square-equal x := w, y := m·n, from 50
  have r410_1 : w ≥ 0 := by parley_order
  have r410_2 : m * n ≥ 0 := by parley_order
  have s51 : w = m * n := by first | linear_combination (norm := parley_norm) ((Parley.Items.Stdlib.Numbers.mun_square_equal (x := w) (y := m * n) (by parley_side) (by parley_side))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_square_equal (x := w) (y := m * n) (by parley_side) (by parley_side))).mp (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := ((Parley.Items.Stdlib.Numbers.mun_square_equal (x := w) (y := m * n) (by parley_side) (by parley_side))).mp (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_square_equal (x := w) (y := m * n) (by parley_side) (by parley_side))).mp (by parley_side) | exact_mod_cast (((Parley.Items.Stdlib.Numbers.mun_square_equal (x := w) (y := m * n) (by parley_side) (by parley_side))).mp (by parley_side)).symm | (have h := ((Parley.Items.Stdlib.Numbers.mun_square_equal (x := w) (y := m * n) (by parley_side) (by parley_side))).mp (by parley_side); rify; linear_combination (norm := parley_norm) h) | (have h := ((Parley.Items.Stdlib.Numbers.mun_square_equal (x := w) (y := m * n) (by parley_side) (by parley_side))).mp (by parley_side); qify; linear_combination (norm := parley_norm) h) | (have h := ((Parley.Items.Stdlib.Numbers.mun_square_equal (x := w) (y := m * n) (by parley_side) (by parley_side))).mp (by parley_side); parley_int_power h) | (have h := ((Parley.Items.Stdlib.Numbers.mun_square_equal (x := w) (y := m * n) (by parley_side) (by parley_side))).mp (by parley_side); parley_side)
  -- 52. substitute w = m·n (line 51) into line 1
  have s52 : a = 2 * (m * n) := by parley_subst_at s51 s1
  -- 53. substitute
  have s53 : b = m ^ 2 - n ^ 2 := by
    have c1 : s = m ^ 2 := by parley_subst s46
    have row1 : b = m ^ 2 - t := by parley_subst_at c1 s22
    have c2 : t = n ^ 2 := by parley_subst s47
    have row2 : b = m ^ 2 - n ^ 2 := by parley_subst_at c2 row1
    exact row2
  -- 54. substitute
  have s54 : c = m ^ 2 + n ^ 2 := by
    have c1 : s = m ^ 2 := by parley_subst s46
    have row1 : c = m ^ 2 + t := by parley_subst_at c1 s18
    have c2 : t = n ^ 2 := by parley_subst s47
    have row2 : c = m ^ 2 + n ^ 2 := by parley_subst_at c2 row1
    exact row2
  -- 55. inequalities, from H2
  have s55 : 0 < b := by parley_order
  -- 56. transitivity, from 55, 53
  have s56 : 0 < m ^ 2 - n ^ 2 := by parley_order
  -- 57. inequalities
  have s57 : n ^ 2 < m ^ 2 := by parley_order
  -- 58. mun:square-less x := n, y := m, from 57
  have r441_1 : n ≥ 0 := by parley_order
  have r441_2 : m ≥ 0 := by parley_order
  have s58 : n < m := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Numbers.mun_square_less (x := n) (y := m) (by parley_side) (by parley_side))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_square_less (x := n) (y := m) (by parley_side) (by parley_side))).mpr (by parley_side); parley_side)
  -- 59. def:gcd a := m, b := n
  have s59a : 0 < (Int.gcd m n : ℤ) := by first | exact (Parley.Items.Stdlib.Divisibility.def_gcd_1 (a := m) (by parley_side) (b := n) (by parley_side)) | exact ((Parley.Items.Stdlib.Divisibility.def_gcd_1 (a := m) (by parley_side) (b := n) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Divisibility.def_gcd_1 (a := m) (by parley_side) (b := n) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.def_gcd_1 (a := m) (by parley_side) (b := n) (by parley_side)) | (have h := (Parley.Items.Stdlib.Divisibility.def_gcd_1 (a := m) (by parley_side) (b := n) (by parley_side)); parley_side)
  have s59b : (Int.gcd m n : ℤ) ∣ m := by first | exact (Parley.Items.Stdlib.Divisibility.def_gcd_2 (a := m) (by parley_side) (b := n) (by parley_side)) | exact ((Parley.Items.Stdlib.Divisibility.def_gcd_2 (a := m) (by parley_side) (b := n) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Divisibility.def_gcd_2 (a := m) (by parley_side) (b := n) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.def_gcd_2 (a := m) (by parley_side) (b := n) (by parley_side)) | (have h := (Parley.Items.Stdlib.Divisibility.def_gcd_2 (a := m) (by parley_side) (b := n) (by parley_side)); parley_side)
  have s59c : (Int.gcd m n : ℤ) ∣ n := by first | exact (Parley.Items.Stdlib.Divisibility.def_gcd_3 (a := m) (by parley_side) (b := n) (by parley_side)) | exact ((Parley.Items.Stdlib.Divisibility.def_gcd_3 (a := m) (by parley_side) (b := n) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Divisibility.def_gcd_3 (a := m) (by parley_side) (b := n) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.def_gcd_3 (a := m) (by parley_side) (b := n) (by parley_side)) | (have h := (Parley.Items.Stdlib.Divisibility.def_gcd_3 (a := m) (by parley_side) (b := n) (by parley_side)); parley_side)
  -- 60. mun:divides-multiple e := gcd(m, n), a := m, x := m, from 59
  have s60 : (Int.gcd m n : ℤ) ∣ m * m := by first | exact (Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := (Int.gcd m n : ℤ)) (a := m) (x := m) s59b) | exact ((Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := (Int.gcd m n : ℤ)) (a := m) (x := m) s59b)).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := (Int.gcd m n : ℤ)) (a := m) (x := m) s59b) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := (Int.gcd m n : ℤ)) (a := m) (x := m) s59b) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := (Int.gcd m n : ℤ)) (a := m) (x := m) s59b); parley_side)
  -- 61. substitute
  have s61 : (Int.gcd m n : ℤ) ∣ s := by
    have c1 : m * m = s := by linear_combination (norm := parley_norm) (-1) * s46
    have row1 : (Int.gcd m n : ℤ) ∣ s := by parley_subst_at c1 s60
    exact row1
  -- 62. mun:divides-multiple e := gcd(m, n), a := n, x := n, from 59
  have s62 : (Int.gcd m n : ℤ) ∣ n * n := by first | exact (Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := (Int.gcd m n : ℤ)) (a := n) (x := n) s59c) | exact ((Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := (Int.gcd m n : ℤ)) (a := n) (x := n) s59c)).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := (Int.gcd m n : ℤ)) (a := n) (x := n) s59c) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := (Int.gcd m n : ℤ)) (a := n) (x := n) s59c) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := (Int.gcd m n : ℤ)) (a := n) (x := n) s59c); parley_side)
  -- 63. substitute
  have s63 : (Int.gcd m n : ℤ) ∣ t := by
    have c1 : n * n = t := by linear_combination (norm := parley_norm) (-1) * s47
    have row1 : (Int.gcd m n : ℤ) ∣ t := by parley_subst_at c1 s62
    exact row1
  -- 64. thm:divides-gcd d := gcd(m, n), a := s, b := t, from 61, 63
  have s64 : (Int.gcd m n : ℤ) ∣ (Int.gcd s t : ℤ) := by first | exact (Parley.Items.Stdlib.Divisibility.thm_divides_gcd (d := (Int.gcd m n : ℤ)) (a := s) (b := t) s61 s63) | exact ((Parley.Items.Stdlib.Divisibility.thm_divides_gcd (d := (Int.gcd m n : ℤ)) (a := s) (b := t) s61 s63)).symm | simpa using (Parley.Items.Stdlib.Divisibility.thm_divides_gcd (d := (Int.gcd m n : ℤ)) (a := s) (b := t) s61 s63) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.thm_divides_gcd (d := (Int.gcd m n : ℤ)) (a := s) (b := t) s61 s63) | (have h := (Parley.Items.Stdlib.Divisibility.thm_divides_gcd (d := (Int.gcd m n : ℤ)) (a := s) (b := t) s61 s63); parley_side)
  -- 65. substitute gcd(s, t) = 1 (line 44) into line 64
  have s65 : (Int.gcd m n : ℤ) ∣ (1 : ℤ) := by first | parley_subst_at s44 s64 | (have e_nat : Int.gcd s t = 1 := by exact_mod_cast s44; parley_subst_at e_nat s64)
  -- 66. mun:divides-one d := gcd(m, n), from 59, 65
  have s66 : (Int.gcd m n : ℤ) = 1 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := (Int.gcd m n : ℤ)) (by parley_side) s65) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := (Int.gcd m n : ℤ)) (by parley_side) s65); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := (Int.gcd m n : ℤ)) (by parley_side) s65); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := (Int.gcd m n : ℤ)) (by parley_side) s65) | exact_mod_cast ((Parley.Items.Stdlib.Divisibility.mun_divides_one (d := (Int.gcd m n : ℤ)) (by parley_side) s65)).symm | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := (Int.gcd m n : ℤ)) (by parley_side) s65); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := (Int.gcd m n : ℤ)) (by parley_side) s65); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := (Int.gcd m n : ℤ)) (by parley_side) s65); parley_int_power h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := (Int.gcd m n : ℤ)) (by parley_side) s65); parley_side)
  -- 67. contradiction
  have s67 : Odd (m + n) := by
    by_contra hc_hS3
    have hS3 : ¬ Odd (m + n) := by parley_suppose hc_hS3
    -- 67.1. mun:even-or-odd n := m + n
    have s67_1 : Even (m + n) ∨ Odd (m + n) := by first | exact (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := m + n)) | exact ((Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := m + n))).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := m + n)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := m + n)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := m + n)); parley_side)
    -- 67.2. mun:disjunctive-syllogism P := m + n is even, Q := m + n is odd, from S3, 67.1
    have s67_2 : Even (m + n) := by first | exact (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism (P := Even (m + n)) (Q := Odd (m + n)) s67_1 hS3) | exact ((Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism (P := Even (m + n)) (Q := Odd (m + n)) s67_1 hS3)).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism (P := Even (m + n)) (Q := Odd (m + n)) s67_1 hS3) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism (P := Even (m + n)) (Q := Odd (m + n)) s67_1 hS3) | (have h := (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism (P := Even (m + n)) (Q := Odd (m + n)) s67_1 hS3); parley_side)
    -- 67.3. obtain u: def:even n := m + n, from 67.2
    obtain ⟨u, s67_3⟩ := ((Parley.Items.Stdlib.Divisibility.def_even (n := m + n))).mp (by parley_side)
    -- 67.4. algebra
    have s67_4 : m ^ 2 - n ^ 2 = (m + n) * (m - n) := by parley_ring
    -- 67.5. substitute m + n = 2u (line 67.3) into line 67.4
    have s67_5 : m ^ 2 - n ^ 2 = 2 * u * (m - n) := by parley_subst_at s67_3 s67_4
    -- 67.6. calculation
    have s67_6 : b = 2 * (u * (m - n)) := by
      calc b = m ^ 2 - n ^ 2 := by parley_side
        _ = 2 * u * (m - n) := by parley_side
        _ = 2 * (u * (m - n)) := by parley_ring
    -- 67.7. def:even n := b, from 67.6
    have s67_7 : Even b := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_even (n := b))).mpr ⟨u * (m - n), by parley_side⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_even (n := b))).mpr ⟨u * (m - n), by parley_side⟩; parley_side)
    -- 67.8. mun:not-both n := b, from 67.7
    have s67_8 : ¬ Odd b := by first | exact (Parley.Items.Stdlib.Divisibility.mun_not_both (n := b) s67_7) | exact ((Parley.Items.Stdlib.Divisibility.mun_not_both (n := b) s67_7)).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_not_both (n := b) s67_7) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_not_both (n := b) s67_7) | (have h := (Parley.Items.Stdlib.Divisibility.mun_not_both (n := b) s67_7); parley_side)
    all_goals parley_side
  -- 68. exhibit, from 53, 54, 58, 66, 67
  have r505_1 : a = 2 * m * n := by linear_combination (norm := parley_norm) s52
  have s68 : ∃ m : ℤ, 0 < m ∧ (∃ n : ℤ, 0 < n ∧ (((((n < m ∧ (Int.gcd m n : ℤ) = 1) ∧ Odd (m + n)) ∧ a = 2 * m * n) ∧ b = m ^ 2 - n ^ 2) ∧ c = m ^ 2 + n ^ 2)) := ⟨m, by parley_side, n, by parley_side, ⟨⟨⟨⟨⟨by parley_side, by parley_side⟩, by parley_side⟩, by parley_side⟩, by parley_side⟩, by parley_side⟩⟩
  all_goals exact s68

end Parley.Proofs.Wiedijk.PythagoreanTriples.PrimitiveTriple
