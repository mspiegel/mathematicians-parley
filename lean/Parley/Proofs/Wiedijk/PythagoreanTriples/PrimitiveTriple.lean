module

public import AlgebraTactics
public import ArithTactics
public import OrderTactics
public import PowerTactics
public import SubstTactics
public import Tactics
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Reasoning
public import Parley.Proofs.Wiedijk.PythagoreanTriples.LegHypotenuseCoprime
public import Parley.Stdlib.Divisibility.CoprimeSquare

/-! Written from proofs/wiedijk/pythagorean-triples.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.PythagoreanTriples.PrimitiveTriple

set_option maxHeartbeats 1800000 in
theorem primitive_triple (a : ℕ) (hH1 : 0 < a) (b : ℕ) (hH2 : 0 < b) (c : ℕ) (hH3 : 0 < c) (hH4 : (a : ℤ) ^ 2 + (b : ℤ) ^ 2 = (c : ℤ) ^ 2) (hH5 : (Int.gcd (a : ℤ) (b : ℤ) : ℤ) = 1) (hH6 : Even (a : ℤ)) :
    (∃ m : ℕ, 0 < m ∧ (∃ n : ℕ, 0 < n ∧ ((((((n : ℤ) < (m : ℤ) ∧ (Int.gcd (m : ℤ) (n : ℤ) : ℤ) = 1) ∧ Odd ((m : ℤ) + (n : ℤ))) ∧ (a : ℤ) = 2 * (m : ℤ) * (n : ℤ)) ∧ (b : ℤ) = (m : ℤ) ^ 2 - (n : ℤ) ^ 2) ∧ (c : ℤ) = (m : ℤ) ^ 2 + (n : ℤ) ^ 2))) := by
  -- 1. obtain w: def:even n := a, from H6
  obtain ⟨w, s1⟩ := ((Parley.Items.Stdlib.Divisibility.def_even (n := (a : ℤ)))).mp (by parley_side)
  -- 2. inequalities, from H1
  have s2 : 0 < (a : ℤ) := by parley_order
  -- 3. substitute a = 2w (line 1) into line 2
  have s3 : 0 < 2 * w := by parley_subst_at s1 s2
  -- 4. mun:pos-int-nat m := w
  have r185_1 : 0 < w := by parley_side
  have s4 : 0 < w := by first | exact (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := w) (by parley_side)) | exact ((Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := w) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := w) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := w) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := w) (by parley_side)); parley_side)
  lift w to ℕ using s4.le
  -- 5. def:divides d := 2, n := a, from 1
  have s5 : (2 : ℤ) ∣ (a : ℤ) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_divides (d := (2 : ℤ)) (n := (a : ℤ)))).mpr ⟨(w : ℤ), by parley_side⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (2 : ℤ)) (n := (a : ℤ)))).mpr ⟨(w : ℤ), by parley_side⟩; parley_side)
  -- 6. contradiction
  have s6 : Odd (b : ℤ) := by
    by_contra hc_hS1
    have hS1 : ¬ Odd (b : ℤ) := by parley_suppose hc_hS1
    -- 6.1. mun:even-or-odd n := b
    have s6_1 : Even (b : ℤ) ∨ Odd (b : ℤ) := by first | exact (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := (b : ℤ))) | exact ((Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := (b : ℤ)))).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := (b : ℤ))) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := (b : ℤ))) | (have h := (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := (b : ℤ))); parley_side)
    -- 6.2. mun:disjunctive-syllogism P := b is even, Q := b is odd, from S1, 6.1
    have s6_2 : Even (b : ℤ) := by first | exact (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism (P := Even (b : ℤ)) (Q := Odd (b : ℤ)) s6_1 hS1) | exact ((Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism (P := Even (b : ℤ)) (Q := Odd (b : ℤ)) s6_1 hS1)).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism (P := Even (b : ℤ)) (Q := Odd (b : ℤ)) s6_1 hS1) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism (P := Even (b : ℤ)) (Q := Odd (b : ℤ)) s6_1 hS1) | (have h := (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism (P := Even (b : ℤ)) (Q := Odd (b : ℤ)) s6_1 hS1); parley_side)
    -- 6.3. obtain v: def:even n := b, from 6.2
    obtain ⟨v, s6_3⟩ := ((Parley.Items.Stdlib.Divisibility.def_even (n := (b : ℤ)))).mp (by parley_side)
    -- 6.4. def:divides d := 2, n := b, from 6.3
    have s6_4 : (2 : ℤ) ∣ (b : ℤ) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_divides (d := (2 : ℤ)) (n := (b : ℤ)))).mpr ⟨v, by parley_side⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (2 : ℤ)) (n := (b : ℤ)))).mpr ⟨v, by parley_side⟩; parley_side)
    -- 6.5. thm:divides-gcd d := 2, from 5, 6.4
    have s6_5 : (2 : ℤ) ∣ (Int.gcd (a : ℤ) (b : ℤ) : ℤ) := by first | exact (Parley.Items.Stdlib.Divisibility.thm_divides_gcd (d := (2 : ℤ)) (a := (a : ℤ)) (b := (b : ℤ)) s5 s6_4) | exact ((Parley.Items.Stdlib.Divisibility.thm_divides_gcd (d := (2 : ℤ)) (a := (a : ℤ)) (b := (b : ℤ)) s5 s6_4)).symm | simpa using (Parley.Items.Stdlib.Divisibility.thm_divides_gcd (d := (2 : ℤ)) (a := (a : ℤ)) (b := (b : ℤ)) s5 s6_4) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.thm_divides_gcd (d := (2 : ℤ)) (a := (a : ℤ)) (b := (b : ℤ)) s5 s6_4) | (have h := (Parley.Items.Stdlib.Divisibility.thm_divides_gcd (d := (2 : ℤ)) (a := (a : ℤ)) (b := (b : ℤ)) s5 s6_4); parley_side)
    -- 6.6. substitute gcd(a, b) = 1 (H5) into line 6.5
    have s6_6 : (2 : ℤ) ∣ (1 : ℤ) := by parley_subst_at hH5 s6_5
    exact absurd s6_6 (by norm_num)
    all_goals parley_side
  -- 7. obtain q: def:odd n := b, from 6
  obtain ⟨q, s7⟩ := ((Parley.Items.Stdlib.Divisibility.def_odd (n := (b : ℤ)))).mp (by parley_side)
  -- 8. substitute
  have s8 : (2 * (w : ℤ)) ^ 2 + (2 * q + 1) ^ 2 = (c : ℤ) ^ 2 := by
    have c1 : (a : ℤ) = 2 * (w : ℤ) := by parley_subst s1
    have row1 : (2 * (w : ℤ)) ^ 2 + (b : ℤ) ^ 2 = (c : ℤ) ^ 2 := by parley_subst_at c1 hH4
    have c2 : (b : ℤ) = 2 * q + 1 := by parley_subst s7
    have row2 : (2 * (w : ℤ)) ^ 2 + (2 * q + 1) ^ 2 = (c : ℤ) ^ 2 := by parley_subst_at c2 row1
    exact row2
  -- 9. contradiction
  have s9 : Odd (c : ℤ) := by
    by_contra hc_hS2
    have hS2 : ¬ Odd (c : ℤ) := by parley_suppose hc_hS2
    -- 9.1. mun:even-or-odd n := c
    have s9_1 : Even (c : ℤ) ∨ Odd (c : ℤ) := by first | exact (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := (c : ℤ))) | exact ((Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := (c : ℤ)))).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := (c : ℤ))) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := (c : ℤ))) | (have h := (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := (c : ℤ))); parley_side)
    -- 9.2. mun:disjunctive-syllogism P := c is even, Q := c is odd, from S2, 9.1
    have s9_2 : Even (c : ℤ) := by first | exact (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism (P := Even (c : ℤ)) (Q := Odd (c : ℤ)) s9_1 hS2) | exact ((Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism (P := Even (c : ℤ)) (Q := Odd (c : ℤ)) s9_1 hS2)).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism (P := Even (c : ℤ)) (Q := Odd (c : ℤ)) s9_1 hS2) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism (P := Even (c : ℤ)) (Q := Odd (c : ℤ)) s9_1 hS2) | (have h := (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism (P := Even (c : ℤ)) (Q := Odd (c : ℤ)) s9_1 hS2); parley_side)
    -- 9.3. obtain r: def:even n := c, from 9.2
    obtain ⟨r, s9_3⟩ := ((Parley.Items.Stdlib.Divisibility.def_even (n := (c : ℤ)))).mp (by parley_side)
    -- 9.4. substitute c = 2r (line 9.3) into line 8
    have s9_4 : (2 * (w : ℤ)) ^ 2 + (2 * q + 1) ^ 2 = (2 * r) ^ 2 := by parley_subst_at s9_3 s8
    -- 9.5. algebra, from 9.4
    have s9_5 : 1 = 2 * (2 * r ^ 2 - 2 * (w : ℤ) ^ 2 - 2 * q ^ 2 - 2 * q) := by linear_combination (norm := parley_norm) s9_4
    -- 9.6. def:divides d := 2, n := 1, from 9.5
    have s9_6 : (2 : ℤ) ∣ (1 : ℤ) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_divides (d := (2 : ℤ)) (n := (1 : ℤ)))).mpr ⟨2 * r ^ 2 - 2 * (w : ℤ) ^ 2 - 2 * q ^ 2 - 2 * q, by parley_side⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (2 : ℤ)) (n := (1 : ℤ)))).mpr ⟨2 * r ^ 2 - 2 * (w : ℤ) ^ 2 - 2 * q ^ 2 - 2 * q, by parley_side⟩; parley_side)
    exact absurd s9_6 (by norm_num)
    all_goals parley_side
  -- 10. obtain r: def:odd n := c, from 9
  obtain ⟨r, s10⟩ := ((Parley.Items.Stdlib.Divisibility.def_odd (n := (c : ℤ)))).mp (by parley_side)
  -- 11. algebra, from 7, 10
  have s11 : (c : ℤ) + (b : ℤ) = 2 * (r + q + 1) := by linear_combination (norm := parley_norm) s7 + s10
  -- 12. def:even n := c + b, from 11
  have s12 : Even ((c : ℤ) + (b : ℤ)) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_even (n := (c : ℤ) + (b : ℤ)))).mpr ⟨r + q + 1, by parley_side⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_even (n := (c : ℤ) + (b : ℤ)))).mpr ⟨r + q + 1, by parley_side⟩; parley_side)
  -- 13. obtain s: def:even n := c + b, from 12
  obtain ⟨s, s13⟩ := ((Parley.Items.Stdlib.Divisibility.def_even (n := (c : ℤ) + (b : ℤ)))).mp (by parley_side)
  -- 14. algebra, from 7, 10
  have s14 : (c : ℤ) - (b : ℤ) = 2 * (r - q) := by linear_combination (norm := parley_norm) (-1) * s7 + s10
  -- 15. def:even n := c − b, from 14
  have s15 : Even ((c : ℤ) - (b : ℤ)) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_even (n := (c : ℤ) - (b : ℤ)))).mpr ⟨r - q, by parley_side⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_even (n := (c : ℤ) - (b : ℤ)))).mpr ⟨r - q, by parley_side⟩; parley_side)
  -- 16. obtain t: def:even n := c − b, from 15
  obtain ⟨t, s16⟩ := ((Parley.Items.Stdlib.Divisibility.def_even (n := (c : ℤ) - (b : ℤ)))).mp (by parley_side)
  -- 17. algebra, from 13, 16
  have s17 : (c : ℤ) * 2 = (s + t) * 2 := by linear_combination (norm := parley_norm) s13 + s16
  -- 18. mun:multiply-cancel a := c, b := s + t, c := 2, from 17
  have r269_1 : (2 : ℤ) ≠ 0 := by parley_arith
  have s18 : (c : ℤ) = s + t := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := (c : ℤ)) (b := s + t) (c := (2 : ℤ)) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := (c : ℤ)) (b := s + t) (c := (2 : ℤ)) (by parley_side) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := (c : ℤ)) (b := s + t) (c := (2 : ℤ)) (by parley_side) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := (c : ℤ)) (b := s + t) (c := (2 : ℤ)) (by parley_side) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := (c : ℤ)) (b := s + t) (c := (2 : ℤ)) (by parley_side) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := (c : ℤ)) (b := s + t) (c := (2 : ℤ)) (by parley_side) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := (c : ℤ)) (b := s + t) (c := (2 : ℤ)) (by parley_side) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := (c : ℤ)) (b := s + t) (c := (2 : ℤ)) (by parley_side) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := (c : ℤ)) (b := s + t) (c := (2 : ℤ)) (by parley_side) (by parley_side)); parley_side)
  -- 19. algebra
  have s19 : (s - t) * 2 = 2 * s - 2 * t := by parley_ring
  -- 20. substitute
  have s20 : (s - t) * 2 = (c : ℤ) + (b : ℤ) - ((c : ℤ) - (b : ℤ)) := by
    have c1 : 2 * s = (c : ℤ) + (b : ℤ) := by parley_subst s13
    have row1 : (s - t) * 2 = (c : ℤ) + (b : ℤ) - 2 * t := by parley_subst_at c1 s19
    have c2 : 2 * t = (c : ℤ) - (b : ℤ) := by parley_subst s16
    have row2 : (s - t) * 2 = (c : ℤ) + (b : ℤ) - ((c : ℤ) - (b : ℤ)) := by parley_subst_at c2 row1
    exact row2
  -- 21. calculation
  have s21 : (b : ℤ) * 2 = (s - t) * 2 := by
    calc (b : ℤ) * 2 = (c : ℤ) + (b : ℤ) - ((c : ℤ) - (b : ℤ)) := by parley_ring
      _ = (s - t) * 2 := by parley_side
  -- 22. mun:multiply-cancel a := b, b := s − t, c := 2, from 21
  have r287_1 : (2 : ℤ) ≠ 0 := by parley_arith
  have s22 : (b : ℤ) = s - t := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := (b : ℤ)) (b := s - t) (c := (2 : ℤ)) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := (b : ℤ)) (b := s - t) (c := (2 : ℤ)) (by parley_side) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := (b : ℤ)) (b := s - t) (c := (2 : ℤ)) (by parley_side) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := (b : ℤ)) (b := s - t) (c := (2 : ℤ)) (by parley_side) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := (b : ℤ)) (b := s - t) (c := (2 : ℤ)) (by parley_side) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := (b : ℤ)) (b := s - t) (c := (2 : ℤ)) (by parley_side) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := (b : ℤ)) (b := s - t) (c := (2 : ℤ)) (by parley_side) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := (b : ℤ)) (b := s - t) (c := (2 : ℤ)) (by parley_side) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := (b : ℤ)) (b := s - t) (c := (2 : ℤ)) (by parley_side) (by parley_side)); parley_side)
  -- 23. mun:square-positive x := a, from H1
  have s23 : (a : ℤ) ^ 2 > 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_square_positive (x := (a : ℤ)) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_square_positive (x := (a : ℤ)) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_square_positive (x := (a : ℤ)) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_square_positive (x := (a : ℤ)) (by parley_side)); parley_side)
  -- 24. inequalities
  have s24 : (b : ℤ) ^ 2 < (a : ℤ) ^ 2 + (b : ℤ) ^ 2 := by parley_order
  -- 25. transitivity, from 24, H4
  have s25 : (b : ℤ) ^ 2 < (c : ℤ) ^ 2 := by parley_order
  -- 26. mun:square-less x := b, y := c, from 25
  have r303_1 : (b : ℤ) ≥ 0 := by parley_order
  have r303_2 : (c : ℤ) ≥ 0 := by parley_order
  have s26 : (b : ℤ) < (c : ℤ) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Numbers.mun_square_less (x := (b : ℤ)) (y := (c : ℤ)) (by parley_side) (by parley_side))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_square_less (x := (b : ℤ)) (y := (c : ℤ)) (by parley_side) (by parley_side))).mpr (by parley_side); parley_side)
  -- 27. inequalities
  have s27 : 0 < (c : ℤ) - (b : ℤ) := by parley_order
  -- 28. substitute c − b = 2t (line 16) into line 27
  have s28 : 0 < 2 * t := by parley_subst_at s16 s27
  -- 29. mun:pos-int-nat m := t
  have r316_1 : 0 < t := by parley_side
  have s29 : 0 < t := by first | exact (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := t) (by parley_side)) | exact ((Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := t) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := t) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := t) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := t) (by parley_side)); parley_side)
  lift t to ℕ using s29.le
  -- 30. inequalities, from H2, H3
  have s30 : 0 < (c : ℤ) + (b : ℤ) := by parley_order
  -- 31. substitute c + b = 2s (line 13) into line 30
  have s31 : 0 < 2 * s := by parley_subst_at s13 s30
  -- 32. mun:pos-int-nat m := s
  have r326_1 : 0 < s := by parley_side
  have s32 : 0 < s := by first | exact (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := s) (by parley_side)) | exact ((Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := s) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := s) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := s) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := s) (by parley_side)); parley_side)
  lift s to ℕ using s32.le
  -- 33. algebra
  have s33 : ((c : ℤ) + (b : ℤ)) * ((c : ℤ) - (b : ℤ)) = (c : ℤ) ^ 2 - (b : ℤ) ^ 2 := by parley_ring
  -- 34. substitute
  have s34 : 2 * (s : ℤ) * (2 * (t : ℤ)) = (c : ℤ) ^ 2 - (b : ℤ) ^ 2 := by
    have c1 : (c : ℤ) + (b : ℤ) = 2 * (s : ℤ) := by parley_subst s13
    have row1 : 2 * (s : ℤ) * ((c : ℤ) - (b : ℤ)) = (c : ℤ) ^ 2 - (b : ℤ) ^ 2 := by parley_subst_at c1 s33
    have c2 : (c : ℤ) - (b : ℤ) = 2 * (t : ℤ) := by parley_subst s16
    have row2 : 2 * (s : ℤ) * (2 * (t : ℤ)) = (c : ℤ) ^ 2 - (b : ℤ) ^ 2 := by parley_subst_at c2 row1
    exact row2
  -- 35. calculation
  have s35 : (w : ℤ) ^ 2 * 4 = (s : ℤ) * (t : ℤ) * 4 := by
    calc (w : ℤ) ^ 2 * 4 = (2 * (w : ℤ)) ^ 2 := by parley_ring
      _ = (a : ℤ) ^ 2 := by parley_subst s1
      _ = (c : ℤ) ^ 2 - (b : ℤ) ^ 2 := by linear_combination (norm := parley_norm) hH4
      _ = 2 * (s : ℤ) * (2 * (t : ℤ)) := by parley_side
      _ = (s : ℤ) * (t : ℤ) * 4 := by parley_ring
  -- 36. mun:multiply-cancel a := w², b := s·t, c := 4, from 35
  have r347_1 : (4 : ℤ) ≠ 0 := by parley_arith
  have s36 : (w : ℤ) ^ 2 = (s : ℤ) * (t : ℤ) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := (w : ℤ) ^ 2) (b := (s : ℤ) * (t : ℤ)) (c := (4 : ℤ)) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := (w : ℤ) ^ 2) (b := (s : ℤ) * (t : ℤ)) (c := (4 : ℤ)) (by parley_side) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := (w : ℤ) ^ 2) (b := (s : ℤ) * (t : ℤ)) (c := (4 : ℤ)) (by parley_side) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := (w : ℤ) ^ 2) (b := (s : ℤ) * (t : ℤ)) (c := (4 : ℤ)) (by parley_side) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := (w : ℤ) ^ 2) (b := (s : ℤ) * (t : ℤ)) (c := (4 : ℤ)) (by parley_side) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := (w : ℤ) ^ 2) (b := (s : ℤ) * (t : ℤ)) (c := (4 : ℤ)) (by parley_side) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := (w : ℤ) ^ 2) (b := (s : ℤ) * (t : ℤ)) (c := (4 : ℤ)) (by parley_side) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := (w : ℤ) ^ 2) (b := (s : ℤ) * (t : ℤ)) (c := (4 : ℤ)) (by parley_side) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := (w : ℤ) ^ 2) (b := (s : ℤ) * (t : ℤ)) (c := (4 : ℤ)) (by parley_side) (by parley_side)); parley_side)
  -- 37. def:gcd a := s, b := t, from 29, 32
  have s37a : 0 < (Int.gcd (s : ℤ) (t : ℤ) : ℤ) := by first | exact (Parley.Items.Stdlib.Divisibility.def_gcd_1 (a := s) (by parley_side) (b := t) (by parley_side)) | exact ((Parley.Items.Stdlib.Divisibility.def_gcd_1 (a := s) (by parley_side) (b := t) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Divisibility.def_gcd_1 (a := s) (by parley_side) (b := t) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.def_gcd_1 (a := s) (by parley_side) (b := t) (by parley_side)) | (have h := (Parley.Items.Stdlib.Divisibility.def_gcd_1 (a := s) (by parley_side) (b := t) (by parley_side)); parley_side)
  have s37b : (Int.gcd (s : ℤ) (t : ℤ) : ℤ) ∣ (s : ℤ) := by first | exact (Parley.Items.Stdlib.Divisibility.def_gcd_2 (a := s) (by parley_side) (b := t) (by parley_side)) | exact ((Parley.Items.Stdlib.Divisibility.def_gcd_2 (a := s) (by parley_side) (b := t) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Divisibility.def_gcd_2 (a := s) (by parley_side) (b := t) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.def_gcd_2 (a := s) (by parley_side) (b := t) (by parley_side)) | (have h := (Parley.Items.Stdlib.Divisibility.def_gcd_2 (a := s) (by parley_side) (b := t) (by parley_side)); parley_side)
  have s37c : (Int.gcd (s : ℤ) (t : ℤ) : ℤ) ∣ (t : ℤ) := by first | exact (Parley.Items.Stdlib.Divisibility.def_gcd_3 (a := s) (by parley_side) (b := t) (by parley_side)) | exact ((Parley.Items.Stdlib.Divisibility.def_gcd_3 (a := s) (by parley_side) (b := t) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Divisibility.def_gcd_3 (a := s) (by parley_side) (b := t) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.def_gcd_3 (a := s) (by parley_side) (b := t) (by parley_side)) | (have h := (Parley.Items.Stdlib.Divisibility.def_gcd_3 (a := s) (by parley_side) (b := t) (by parley_side)); parley_side)
  -- 38. mun:divides-sum d := gcd(s, t), a := s, b := t, from 37
  have s38 : (Int.gcd (s : ℤ) (t : ℤ) : ℤ) ∣ (s : ℤ) + (t : ℤ) := by first | exact (Parley.Items.Stdlib.Divisibility.mun_divides_sum (d := (Int.gcd (s : ℤ) (t : ℤ) : ℤ)) (a := (s : ℤ)) (b := (t : ℤ)) s37b s37c) | exact ((Parley.Items.Stdlib.Divisibility.mun_divides_sum (d := (Int.gcd (s : ℤ) (t : ℤ) : ℤ)) (a := (s : ℤ)) (b := (t : ℤ)) s37b s37c)).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_divides_sum (d := (Int.gcd (s : ℤ) (t : ℤ) : ℤ)) (a := (s : ℤ)) (b := (t : ℤ)) s37b s37c) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_divides_sum (d := (Int.gcd (s : ℤ) (t : ℤ) : ℤ)) (a := (s : ℤ)) (b := (t : ℤ)) s37b s37c) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_sum (d := (Int.gcd (s : ℤ) (t : ℤ) : ℤ)) (a := (s : ℤ)) (b := (t : ℤ)) s37b s37c); parley_side)
  -- 39. substitute c = s + t (line 18) into line 38
  have s39 : (Int.gcd (s : ℤ) (t : ℤ) : ℤ) ∣ (c : ℤ) := by parley_subst_at s18 s38
  -- 40. mun:divides-difference d := gcd(s, t), a := s, b := t, from 37
  have s40 : (Int.gcd (s : ℤ) (t : ℤ) : ℤ) ∣ (s : ℤ) - (t : ℤ) := by first | exact (Parley.Items.Stdlib.Divisibility.mun_divides_difference (d := (Int.gcd (s : ℤ) (t : ℤ) : ℤ)) (a := (s : ℤ)) (b := (t : ℤ)) s37b s37c) | exact ((Parley.Items.Stdlib.Divisibility.mun_divides_difference (d := (Int.gcd (s : ℤ) (t : ℤ) : ℤ)) (a := (s : ℤ)) (b := (t : ℤ)) s37b s37c)).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_divides_difference (d := (Int.gcd (s : ℤ) (t : ℤ) : ℤ)) (a := (s : ℤ)) (b := (t : ℤ)) s37b s37c) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_divides_difference (d := (Int.gcd (s : ℤ) (t : ℤ) : ℤ)) (a := (s : ℤ)) (b := (t : ℤ)) s37b s37c) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_difference (d := (Int.gcd (s : ℤ) (t : ℤ) : ℤ)) (a := (s : ℤ)) (b := (t : ℤ)) s37b s37c); parley_side)
  -- 41. substitute b = s − t (line 22) into line 40
  have s41 : (Int.gcd (s : ℤ) (t : ℤ) : ℤ) ∣ (b : ℤ) := by parley_subst_at s22 s40
  -- 42. thm:divides-gcd d := gcd(s, t), a := b, b := c, from 39, 41
  have s42 : (Int.gcd (s : ℤ) (t : ℤ) : ℤ) ∣ (Int.gcd (b : ℤ) (c : ℤ) : ℤ) := by first | exact (Parley.Items.Stdlib.Divisibility.thm_divides_gcd (d := (Int.gcd (s : ℤ) (t : ℤ) : ℤ)) (a := (b : ℤ)) (b := (c : ℤ)) s41 s39) | exact ((Parley.Items.Stdlib.Divisibility.thm_divides_gcd (d := (Int.gcd (s : ℤ) (t : ℤ) : ℤ)) (a := (b : ℤ)) (b := (c : ℤ)) s41 s39)).symm | simpa using (Parley.Items.Stdlib.Divisibility.thm_divides_gcd (d := (Int.gcd (s : ℤ) (t : ℤ) : ℤ)) (a := (b : ℤ)) (b := (c : ℤ)) s41 s39) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.thm_divides_gcd (d := (Int.gcd (s : ℤ) (t : ℤ) : ℤ)) (a := (b : ℤ)) (b := (c : ℤ)) s41 s39) | (have h := (Parley.Items.Stdlib.Divisibility.thm_divides_gcd (d := (Int.gcd (s : ℤ) (t : ℤ) : ℤ)) (a := (b : ℤ)) (b := (c : ℤ)) s41 s39); parley_side)
  -- 43. substitute
  have s43 : (Int.gcd (s : ℤ) (t : ℤ) : ℤ) ∣ (1 : ℤ) := by
    have c1 : (Int.gcd (b : ℤ) (c : ℤ) : ℤ) = 1 := by first | linear_combination (norm := parley_norm) (Parley.Proofs.Wiedijk.PythagoreanTriples.LegHypotenuseCoprime.leg_hypotenuse_coprime (a := a) (by parley_side) (b := b) (by parley_side) (c := c) (by parley_side) (by parley_side) (by parley_side)) | (have h := (Parley.Proofs.Wiedijk.PythagoreanTriples.LegHypotenuseCoprime.leg_hypotenuse_coprime (a := a) (by parley_side) (b := b) (by parley_side) (c := c) (by parley_side) (by parley_side) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Wiedijk.PythagoreanTriples.LegHypotenuseCoprime.leg_hypotenuse_coprime (a := a) (by parley_side) (b := b) (by parley_side) (c := c) (by parley_side) (by parley_side) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Proofs.Wiedijk.PythagoreanTriples.LegHypotenuseCoprime.leg_hypotenuse_coprime (a := a) (by parley_side) (b := b) (by parley_side) (c := c) (by parley_side) (by parley_side) (by parley_side)) | exact_mod_cast ((Parley.Proofs.Wiedijk.PythagoreanTriples.LegHypotenuseCoprime.leg_hypotenuse_coprime (a := a) (by parley_side) (b := b) (by parley_side) (c := c) (by parley_side) (by parley_side) (by parley_side))).symm | (have h := (Parley.Proofs.Wiedijk.PythagoreanTriples.LegHypotenuseCoprime.leg_hypotenuse_coprime (a := a) (by parley_side) (b := b) (by parley_side) (c := c) (by parley_side) (by parley_side) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Wiedijk.PythagoreanTriples.LegHypotenuseCoprime.leg_hypotenuse_coprime (a := a) (by parley_side) (b := b) (by parley_side) (c := c) (by parley_side) (by parley_side) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Wiedijk.PythagoreanTriples.LegHypotenuseCoprime.leg_hypotenuse_coprime (a := a) (by parley_side) (b := b) (by parley_side) (c := c) (by parley_side) (by parley_side) (by parley_side)); parley_int_power h) | (have h := (Parley.Proofs.Wiedijk.PythagoreanTriples.LegHypotenuseCoprime.leg_hypotenuse_coprime (a := a) (by parley_side) (b := b) (by parley_side) (c := c) (by parley_side) (by parley_side) (by parley_side)); parley_side)
    have row1 : (Int.gcd (s : ℤ) (t : ℤ) : ℤ) ∣ (1 : ℤ) := by parley_subst_at c1 s42
    exact row1
  -- 44. mun:divides-one d := gcd(s, t), from 37, 43
  have s44 : (Int.gcd (s : ℤ) (t : ℤ) : ℤ) = 1 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := Int.gcd (s : ℤ) (t : ℤ)) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := Int.gcd (s : ℤ) (t : ℤ)) (by parley_side) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := Int.gcd (s : ℤ) (t : ℤ)) (by parley_side) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := Int.gcd (s : ℤ) (t : ℤ)) (by parley_side) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Divisibility.mun_divides_one (d := Int.gcd (s : ℤ) (t : ℤ)) (by parley_side) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := Int.gcd (s : ℤ) (t : ℤ)) (by parley_side) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := Int.gcd (s : ℤ) (t : ℤ)) (by parley_side) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := Int.gcd (s : ℤ) (t : ℤ)) (by parley_side) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := Int.gcd (s : ℤ) (t : ℤ)) (by parley_side) (by parley_side)); parley_side)
  -- 45. thm:coprime-square, from 4, 29, 32, 36, 44
  have s45a : (s : ℤ) = (Int.gcd (s : ℤ) (w : ℤ) : ℤ) ^ 2 := by first | linear_combination (norm := parley_norm) (Parley.Stdlib.Divisibility.CoprimeSquare.coprime_square (s := s) (by parley_side) (t := t) (by parley_side) (w := w) (by parley_side) (by parley_side) (by parley_side)).1 | (have h := (Parley.Stdlib.Divisibility.CoprimeSquare.coprime_square (s := s) (by parley_side) (t := t) (by parley_side) (w := w) (by parley_side) (by parley_side) (by parley_side)).1; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Stdlib.Divisibility.CoprimeSquare.coprime_square (s := s) (by parley_side) (t := t) (by parley_side) (w := w) (by parley_side) (by parley_side) (by parley_side)).1; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Stdlib.Divisibility.CoprimeSquare.coprime_square (s := s) (by parley_side) (t := t) (by parley_side) (w := w) (by parley_side) (by parley_side) (by parley_side)).1 | exact_mod_cast ((Parley.Stdlib.Divisibility.CoprimeSquare.coprime_square (s := s) (by parley_side) (t := t) (by parley_side) (w := w) (by parley_side) (by parley_side) (by parley_side)).1).symm | (have h := (Parley.Stdlib.Divisibility.CoprimeSquare.coprime_square (s := s) (by parley_side) (t := t) (by parley_side) (w := w) (by parley_side) (by parley_side) (by parley_side)).1; rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Stdlib.Divisibility.CoprimeSquare.coprime_square (s := s) (by parley_side) (t := t) (by parley_side) (w := w) (by parley_side) (by parley_side) (by parley_side)).1; qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Stdlib.Divisibility.CoprimeSquare.coprime_square (s := s) (by parley_side) (t := t) (by parley_side) (w := w) (by parley_side) (by parley_side) (by parley_side)).1; parley_int_power h) | (have h := (Parley.Stdlib.Divisibility.CoprimeSquare.coprime_square (s := s) (by parley_side) (t := t) (by parley_side) (w := w) (by parley_side) (by parley_side) (by parley_side)).1; parley_side)
  have s45b : (t : ℤ) = (Int.gcd (t : ℤ) (w : ℤ) : ℤ) ^ 2 := by first | linear_combination (norm := parley_norm) (Parley.Stdlib.Divisibility.CoprimeSquare.coprime_square (s := s) (by parley_side) (t := t) (by parley_side) (w := w) (by parley_side) (by parley_side) (by parley_side)).2 | (have h := (Parley.Stdlib.Divisibility.CoprimeSquare.coprime_square (s := s) (by parley_side) (t := t) (by parley_side) (w := w) (by parley_side) (by parley_side) (by parley_side)).2; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Stdlib.Divisibility.CoprimeSquare.coprime_square (s := s) (by parley_side) (t := t) (by parley_side) (w := w) (by parley_side) (by parley_side) (by parley_side)).2; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Stdlib.Divisibility.CoprimeSquare.coprime_square (s := s) (by parley_side) (t := t) (by parley_side) (w := w) (by parley_side) (by parley_side) (by parley_side)).2 | exact_mod_cast ((Parley.Stdlib.Divisibility.CoprimeSquare.coprime_square (s := s) (by parley_side) (t := t) (by parley_side) (w := w) (by parley_side) (by parley_side) (by parley_side)).2).symm | (have h := (Parley.Stdlib.Divisibility.CoprimeSquare.coprime_square (s := s) (by parley_side) (t := t) (by parley_side) (w := w) (by parley_side) (by parley_side) (by parley_side)).2; rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Stdlib.Divisibility.CoprimeSquare.coprime_square (s := s) (by parley_side) (t := t) (by parley_side) (w := w) (by parley_side) (by parley_side) (by parley_side)).2; qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Stdlib.Divisibility.CoprimeSquare.coprime_square (s := s) (by parley_side) (t := t) (by parley_side) (w := w) (by parley_side) (by parley_side) (by parley_side)).2; parley_int_power h) | (have h := (Parley.Stdlib.Divisibility.CoprimeSquare.coprime_square (s := s) (by parley_side) (t := t) (by parley_side) (w := w) (by parley_side) (by parley_side) (by parley_side)).2; parley_side)
  set m : ℤ := (Int.gcd (s : ℤ) (w : ℤ) : ℤ) with hD1
  have hD1_kind : 0 < (Int.gcd (s : ℤ) (w : ℤ) : ℤ) := by first | exact (Parley.Items.Stdlib.Divisibility.def_gcd_1 (a := s) (by parley_side) (b := w) (by parley_side)) | exact ((Parley.Items.Stdlib.Divisibility.def_gcd_1 (a := s) (by parley_side) (b := w) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Divisibility.def_gcd_1 (a := s) (by parley_side) (b := w) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.def_gcd_1 (a := s) (by parley_side) (b := w) (by parley_side)) | (have h := (Parley.Items.Stdlib.Divisibility.def_gcd_1 (a := s) (by parley_side) (b := w) (by parley_side)); parley_side)
  -- 46. calculation
  have s46 : (s : ℤ) = m ^ 2 := by
    calc (s : ℤ) = (Int.gcd (s : ℤ) (w : ℤ) : ℤ) ^ 2 := by parley_side
      _ = m ^ 2 := by first | (simp (disch := omega) only [hD1]; push_cast; norm_num; done) | parley_side
  set n : ℤ := (Int.gcd (t : ℤ) (w : ℤ) : ℤ) with hD2
  have hD2_kind : 0 < (Int.gcd (t : ℤ) (w : ℤ) : ℤ) := by first | exact (Parley.Items.Stdlib.Divisibility.def_gcd_1 (a := t) (by parley_side) (b := w) (by parley_side)) | exact ((Parley.Items.Stdlib.Divisibility.def_gcd_1 (a := t) (by parley_side) (b := w) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Divisibility.def_gcd_1 (a := t) (by parley_side) (b := w) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.def_gcd_1 (a := t) (by parley_side) (b := w) (by parley_side)) | (have h := (Parley.Items.Stdlib.Divisibility.def_gcd_1 (a := t) (by parley_side) (b := w) (by parley_side)); parley_side)
  -- 47. calculation
  have s47 : (t : ℤ) = n ^ 2 := by
    calc (t : ℤ) = (Int.gcd (t : ℤ) (w : ℤ) : ℤ) ^ 2 := by parley_side
      _ = n ^ 2 := by first | (simp (disch := omega) only [hD2]; push_cast; norm_num; done) | parley_side
  -- 48. substitute
  have s48 : (w : ℤ) ^ 2 = m ^ 2 * n ^ 2 := by
    have c1 : (s : ℤ) = m ^ 2 := by parley_subst s46
    have row1 : (w : ℤ) ^ 2 = m ^ 2 * (t : ℤ) := by parley_subst_at c1 s36
    have c2 : (t : ℤ) = n ^ 2 := by parley_subst s47
    have row2 : (w : ℤ) ^ 2 = m ^ 2 * n ^ 2 := by parley_subst_at c2 row1
    exact row2
  -- 49. membership
  have s49 : 0 < m * n := by parley_side
  -- 50. algebra, from 48
  have s50 : (w : ℤ) ^ 2 = (m * n) ^ 2 := by linear_combination (norm := parley_norm) s48
  -- 51. mun:square-equal x := w, y := m·n, from 50
  have r410_1 : (w : ℤ) ≥ 0 := by parley_order
  have r410_2 : m * n ≥ 0 := by parley_order
  have s51 : (w : ℤ) = m * n := by first | linear_combination (norm := parley_norm) ((Parley.Items.Stdlib.Numbers.mun_square_equal (x := (w : ℤ)) (y := m * n) (by parley_side) (by parley_side))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_square_equal (x := (w : ℤ)) (y := m * n) (by parley_side) (by parley_side))).mp (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := ((Parley.Items.Stdlib.Numbers.mun_square_equal (x := (w : ℤ)) (y := m * n) (by parley_side) (by parley_side))).mp (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_square_equal (x := (w : ℤ)) (y := m * n) (by parley_side) (by parley_side))).mp (by parley_side) | exact_mod_cast (((Parley.Items.Stdlib.Numbers.mun_square_equal (x := (w : ℤ)) (y := m * n) (by parley_side) (by parley_side))).mp (by parley_side)).symm | (have h := ((Parley.Items.Stdlib.Numbers.mun_square_equal (x := (w : ℤ)) (y := m * n) (by parley_side) (by parley_side))).mp (by parley_side); rify; linear_combination (norm := parley_norm) h) | (have h := ((Parley.Items.Stdlib.Numbers.mun_square_equal (x := (w : ℤ)) (y := m * n) (by parley_side) (by parley_side))).mp (by parley_side); qify; linear_combination (norm := parley_norm) h) | (have h := ((Parley.Items.Stdlib.Numbers.mun_square_equal (x := (w : ℤ)) (y := m * n) (by parley_side) (by parley_side))).mp (by parley_side); parley_int_power h) | (have h := ((Parley.Items.Stdlib.Numbers.mun_square_equal (x := (w : ℤ)) (y := m * n) (by parley_side) (by parley_side))).mp (by parley_side); parley_side)
  -- 52. substitute w = m·n (line 51) into line 1
  have s52 : (a : ℤ) = 2 * (m * n) := by parley_subst_at s51 s1
  -- 53. substitute
  have s53 : (b : ℤ) = m ^ 2 - n ^ 2 := by
    have c1 : (s : ℤ) = m ^ 2 := by parley_subst s46
    have row1 : (b : ℤ) = m ^ 2 - (t : ℤ) := by parley_subst_at c1 s22
    have c2 : (t : ℤ) = n ^ 2 := by parley_subst s47
    have row2 : (b : ℤ) = m ^ 2 - n ^ 2 := by parley_subst_at c2 row1
    exact row2
  -- 54. substitute
  have s54 : (c : ℤ) = m ^ 2 + n ^ 2 := by
    have c1 : (s : ℤ) = m ^ 2 := by parley_subst s46
    have row1 : (c : ℤ) = m ^ 2 + (t : ℤ) := by parley_subst_at c1 s18
    have c2 : (t : ℤ) = n ^ 2 := by parley_subst s47
    have row2 : (c : ℤ) = m ^ 2 + n ^ 2 := by parley_subst_at c2 row1
    exact row2
  -- 55. inequalities, from H2
  have s55 : 0 < (b : ℤ) := by parley_order
  -- 56. transitivity, from 55, 53
  have s56 : 0 < m ^ 2 - n ^ 2 := by parley_order
  -- 57. inequalities
  have s57 : n ^ 2 < m ^ 2 := by parley_order
  -- 58. mun:square-less x := n, y := m, from 57
  have r441_1 : n ≥ 0 := by parley_order
  have r441_2 : m ≥ 0 := by parley_order
  have s58 : n < m := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Numbers.mun_square_less (x := n) (y := m) (by parley_side) (by parley_side))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_square_less (x := n) (y := m) (by parley_side) (by parley_side))).mpr (by parley_side); parley_side)
  -- 59. def:gcd a := m, b := n
  have s59a : 0 < (Int.gcd m n : ℤ) := by first | (have h := (Int.toNat_of_nonneg (show (0 : ℤ) ≤ n by parley_side) ▸ (Int.toNat_of_nonneg (show (0 : ℤ) ≤ m by parley_side) ▸ (Parley.Items.Stdlib.Divisibility.def_gcd_1 (a := m.toNat) (by (try rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ m by parley_side)]); parley_side) (b := n.toNat) (by (try rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ m by parley_side), Int.toNat_of_nonneg (show (0 : ℤ) ≤ n by parley_side)]); parley_side)))); exact h) | (have h := (Int.toNat_of_nonneg (show (0 : ℤ) ≤ n by parley_side) ▸ (Int.toNat_of_nonneg (show (0 : ℤ) ≤ m by parley_side) ▸ (Parley.Items.Stdlib.Divisibility.def_gcd_1 (a := m.toNat) (by (try rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ m by parley_side)]); parley_side) (b := n.toNat) (by (try rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ m by parley_side), Int.toNat_of_nonneg (show (0 : ℤ) ≤ n by parley_side)]); parley_side)))); exact h.symm) | (have h := (Int.toNat_of_nonneg (show (0 : ℤ) ≤ n by parley_side) ▸ (Int.toNat_of_nonneg (show (0 : ℤ) ≤ m by parley_side) ▸ (Parley.Items.Stdlib.Divisibility.def_gcd_1 (a := m.toNat) (by (try rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ m by parley_side)]); parley_side) (b := n.toNat) (by (try rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ m by parley_side), Int.toNat_of_nonneg (show (0 : ℤ) ≤ n by parley_side)]); parley_side)))); simpa using h) | (have h := (Int.toNat_of_nonneg (show (0 : ℤ) ≤ n by parley_side) ▸ (Int.toNat_of_nonneg (show (0 : ℤ) ≤ m by parley_side) ▸ (Parley.Items.Stdlib.Divisibility.def_gcd_1 (a := m.toNat) (by (try rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ m by parley_side)]); parley_side) (b := n.toNat) (by (try rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ m by parley_side), Int.toNat_of_nonneg (show (0 : ℤ) ≤ n by parley_side)]); parley_side)))); exact_mod_cast h) | (have h := (Int.toNat_of_nonneg (show (0 : ℤ) ≤ n by parley_side) ▸ (Int.toNat_of_nonneg (show (0 : ℤ) ≤ m by parley_side) ▸ (Parley.Items.Stdlib.Divisibility.def_gcd_1 (a := m.toNat) (by (try rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ m by parley_side)]); parley_side) (b := n.toNat) (by (try rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ m by parley_side), Int.toNat_of_nonneg (show (0 : ℤ) ≤ n by parley_side)]); parley_side)))); simp (disch := parley_side) only [parley_cast_toNat] at h; (try push_cast at h ⊢); exact h) | (have h := (Int.toNat_of_nonneg (show (0 : ℤ) ≤ n by parley_side) ▸ (Int.toNat_of_nonneg (show (0 : ℤ) ≤ m by parley_side) ▸ (Parley.Items.Stdlib.Divisibility.def_gcd_1 (a := m.toNat) (by (try rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ m by parley_side)]); parley_side) (b := n.toNat) (by (try rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ m by parley_side), Int.toNat_of_nonneg (show (0 : ℤ) ≤ n by parley_side)]); parley_side)))); parley_side)
  have s59b : (Int.gcd m n : ℤ) ∣ m := by first | (have h := (Int.toNat_of_nonneg (show (0 : ℤ) ≤ n by parley_side) ▸ (Int.toNat_of_nonneg (show (0 : ℤ) ≤ m by parley_side) ▸ (Parley.Items.Stdlib.Divisibility.def_gcd_2 (a := m.toNat) (by (try rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ m by parley_side)]); parley_side) (b := n.toNat) (by (try rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ m by parley_side), Int.toNat_of_nonneg (show (0 : ℤ) ≤ n by parley_side)]); parley_side)))); exact h) | (have h := (Int.toNat_of_nonneg (show (0 : ℤ) ≤ n by parley_side) ▸ (Int.toNat_of_nonneg (show (0 : ℤ) ≤ m by parley_side) ▸ (Parley.Items.Stdlib.Divisibility.def_gcd_2 (a := m.toNat) (by (try rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ m by parley_side)]); parley_side) (b := n.toNat) (by (try rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ m by parley_side), Int.toNat_of_nonneg (show (0 : ℤ) ≤ n by parley_side)]); parley_side)))); exact h.symm) | (have h := (Int.toNat_of_nonneg (show (0 : ℤ) ≤ n by parley_side) ▸ (Int.toNat_of_nonneg (show (0 : ℤ) ≤ m by parley_side) ▸ (Parley.Items.Stdlib.Divisibility.def_gcd_2 (a := m.toNat) (by (try rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ m by parley_side)]); parley_side) (b := n.toNat) (by (try rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ m by parley_side), Int.toNat_of_nonneg (show (0 : ℤ) ≤ n by parley_side)]); parley_side)))); simpa using h) | (have h := (Int.toNat_of_nonneg (show (0 : ℤ) ≤ n by parley_side) ▸ (Int.toNat_of_nonneg (show (0 : ℤ) ≤ m by parley_side) ▸ (Parley.Items.Stdlib.Divisibility.def_gcd_2 (a := m.toNat) (by (try rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ m by parley_side)]); parley_side) (b := n.toNat) (by (try rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ m by parley_side), Int.toNat_of_nonneg (show (0 : ℤ) ≤ n by parley_side)]); parley_side)))); exact_mod_cast h) | (have h := (Int.toNat_of_nonneg (show (0 : ℤ) ≤ n by parley_side) ▸ (Int.toNat_of_nonneg (show (0 : ℤ) ≤ m by parley_side) ▸ (Parley.Items.Stdlib.Divisibility.def_gcd_2 (a := m.toNat) (by (try rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ m by parley_side)]); parley_side) (b := n.toNat) (by (try rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ m by parley_side), Int.toNat_of_nonneg (show (0 : ℤ) ≤ n by parley_side)]); parley_side)))); simp (disch := parley_side) only [parley_cast_toNat] at h; (try push_cast at h ⊢); exact h) | (have h := (Int.toNat_of_nonneg (show (0 : ℤ) ≤ n by parley_side) ▸ (Int.toNat_of_nonneg (show (0 : ℤ) ≤ m by parley_side) ▸ (Parley.Items.Stdlib.Divisibility.def_gcd_2 (a := m.toNat) (by (try rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ m by parley_side)]); parley_side) (b := n.toNat) (by (try rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ m by parley_side), Int.toNat_of_nonneg (show (0 : ℤ) ≤ n by parley_side)]); parley_side)))); parley_side)
  have s59c : (Int.gcd m n : ℤ) ∣ n := by first | (have h := (Int.toNat_of_nonneg (show (0 : ℤ) ≤ n by parley_side) ▸ (Int.toNat_of_nonneg (show (0 : ℤ) ≤ m by parley_side) ▸ (Parley.Items.Stdlib.Divisibility.def_gcd_3 (a := m.toNat) (by (try rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ m by parley_side)]); parley_side) (b := n.toNat) (by (try rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ m by parley_side), Int.toNat_of_nonneg (show (0 : ℤ) ≤ n by parley_side)]); parley_side)))); exact h) | (have h := (Int.toNat_of_nonneg (show (0 : ℤ) ≤ n by parley_side) ▸ (Int.toNat_of_nonneg (show (0 : ℤ) ≤ m by parley_side) ▸ (Parley.Items.Stdlib.Divisibility.def_gcd_3 (a := m.toNat) (by (try rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ m by parley_side)]); parley_side) (b := n.toNat) (by (try rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ m by parley_side), Int.toNat_of_nonneg (show (0 : ℤ) ≤ n by parley_side)]); parley_side)))); exact h.symm) | (have h := (Int.toNat_of_nonneg (show (0 : ℤ) ≤ n by parley_side) ▸ (Int.toNat_of_nonneg (show (0 : ℤ) ≤ m by parley_side) ▸ (Parley.Items.Stdlib.Divisibility.def_gcd_3 (a := m.toNat) (by (try rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ m by parley_side)]); parley_side) (b := n.toNat) (by (try rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ m by parley_side), Int.toNat_of_nonneg (show (0 : ℤ) ≤ n by parley_side)]); parley_side)))); simpa using h) | (have h := (Int.toNat_of_nonneg (show (0 : ℤ) ≤ n by parley_side) ▸ (Int.toNat_of_nonneg (show (0 : ℤ) ≤ m by parley_side) ▸ (Parley.Items.Stdlib.Divisibility.def_gcd_3 (a := m.toNat) (by (try rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ m by parley_side)]); parley_side) (b := n.toNat) (by (try rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ m by parley_side), Int.toNat_of_nonneg (show (0 : ℤ) ≤ n by parley_side)]); parley_side)))); exact_mod_cast h) | (have h := (Int.toNat_of_nonneg (show (0 : ℤ) ≤ n by parley_side) ▸ (Int.toNat_of_nonneg (show (0 : ℤ) ≤ m by parley_side) ▸ (Parley.Items.Stdlib.Divisibility.def_gcd_3 (a := m.toNat) (by (try rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ m by parley_side)]); parley_side) (b := n.toNat) (by (try rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ m by parley_side), Int.toNat_of_nonneg (show (0 : ℤ) ≤ n by parley_side)]); parley_side)))); simp (disch := parley_side) only [parley_cast_toNat] at h; (try push_cast at h ⊢); exact h) | (have h := (Int.toNat_of_nonneg (show (0 : ℤ) ≤ n by parley_side) ▸ (Int.toNat_of_nonneg (show (0 : ℤ) ≤ m by parley_side) ▸ (Parley.Items.Stdlib.Divisibility.def_gcd_3 (a := m.toNat) (by (try rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ m by parley_side)]); parley_side) (b := n.toNat) (by (try rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ m by parley_side), Int.toNat_of_nonneg (show (0 : ℤ) ≤ n by parley_side)]); parley_side)))); parley_side)
  -- 60. mun:divides-multiple e := gcd(m, n), a := m, x := m, from 59
  have s60 : (Int.gcd m n : ℤ) ∣ m * m := by first | exact (Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := (Int.gcd m n : ℤ)) (a := m) (x := m) s59b) | exact ((Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := (Int.gcd m n : ℤ)) (a := m) (x := m) s59b)).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := (Int.gcd m n : ℤ)) (a := m) (x := m) s59b) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := (Int.gcd m n : ℤ)) (a := m) (x := m) s59b) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := (Int.gcd m n : ℤ)) (a := m) (x := m) s59b); parley_side)
  -- 61. substitute
  have s61 : (Int.gcd m n : ℤ) ∣ (s : ℤ) := by
    have c1 : m * m = (s : ℤ) := by linear_combination (norm := parley_norm) (-1) * s46
    have row1 : (Int.gcd m n : ℤ) ∣ (s : ℤ) := by parley_subst_at c1 s60
    exact row1
  -- 62. mun:divides-multiple e := gcd(m, n), a := n, x := n, from 59
  have s62 : (Int.gcd m n : ℤ) ∣ n * n := by first | exact (Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := (Int.gcd m n : ℤ)) (a := n) (x := n) s59c) | exact ((Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := (Int.gcd m n : ℤ)) (a := n) (x := n) s59c)).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := (Int.gcd m n : ℤ)) (a := n) (x := n) s59c) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := (Int.gcd m n : ℤ)) (a := n) (x := n) s59c) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := (Int.gcd m n : ℤ)) (a := n) (x := n) s59c); parley_side)
  -- 63. substitute
  have s63 : (Int.gcd m n : ℤ) ∣ (t : ℤ) := by
    have c1 : n * n = (t : ℤ) := by linear_combination (norm := parley_norm) (-1) * s47
    have row1 : (Int.gcd m n : ℤ) ∣ (t : ℤ) := by parley_subst_at c1 s62
    exact row1
  -- 64. thm:divides-gcd d := gcd(m, n), a := s, b := t, from 61, 63
  have s64 : (Int.gcd m n : ℤ) ∣ (Int.gcd (s : ℤ) (t : ℤ) : ℤ) := by first | exact (Parley.Items.Stdlib.Divisibility.thm_divides_gcd (d := (Int.gcd m n : ℤ)) (a := (s : ℤ)) (b := (t : ℤ)) s61 s63) | exact ((Parley.Items.Stdlib.Divisibility.thm_divides_gcd (d := (Int.gcd m n : ℤ)) (a := (s : ℤ)) (b := (t : ℤ)) s61 s63)).symm | simpa using (Parley.Items.Stdlib.Divisibility.thm_divides_gcd (d := (Int.gcd m n : ℤ)) (a := (s : ℤ)) (b := (t : ℤ)) s61 s63) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.thm_divides_gcd (d := (Int.gcd m n : ℤ)) (a := (s : ℤ)) (b := (t : ℤ)) s61 s63) | (have h := (Parley.Items.Stdlib.Divisibility.thm_divides_gcd (d := (Int.gcd m n : ℤ)) (a := (s : ℤ)) (b := (t : ℤ)) s61 s63); parley_side)
  -- 65. substitute gcd(s, t) = 1 (line 44) into line 64
  have s65 : (Int.gcd m n : ℤ) ∣ (1 : ℤ) := by parley_subst_at s44 s64
  -- 66. mun:divides-one d := gcd(m, n), from 59, 65
  have s66 : (Int.gcd m n : ℤ) = 1 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := Int.gcd m n) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := Int.gcd m n) (by parley_side) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := Int.gcd m n) (by parley_side) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := Int.gcd m n) (by parley_side) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Divisibility.mun_divides_one (d := Int.gcd m n) (by parley_side) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := Int.gcd m n) (by parley_side) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := Int.gcd m n) (by parley_side) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := Int.gcd m n) (by parley_side) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := Int.gcd m n) (by parley_side) (by parley_side)); parley_side)
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
    have s67_6 : (b : ℤ) = 2 * (u * (m - n)) := by
      calc (b : ℤ) = m ^ 2 - n ^ 2 := by parley_side
        _ = 2 * u * (m - n) := by parley_side
        _ = 2 * (u * (m - n)) := by parley_ring
    -- 67.7. def:even n := b, from 67.6
    have s67_7 : Even (b : ℤ) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_even (n := (b : ℤ)))).mpr ⟨u * (m - n), by parley_side⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_even (n := (b : ℤ)))).mpr ⟨u * (m - n), by parley_side⟩; parley_side)
    -- 67.8. mun:not-both n := b, from 67.7
    have s67_8 : ¬ Odd (b : ℤ) := by first | exact (Parley.Items.Stdlib.Divisibility.mun_not_both (n := (b : ℤ)) s67_7) | exact ((Parley.Items.Stdlib.Divisibility.mun_not_both (n := (b : ℤ)) s67_7)).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_not_both (n := (b : ℤ)) s67_7) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_not_both (n := (b : ℤ)) s67_7) | (have h := (Parley.Items.Stdlib.Divisibility.mun_not_both (n := (b : ℤ)) s67_7); parley_side)
    all_goals parley_side
  -- 68. exhibit, from 53, 54, 58, 66, 67
  have r505_1 : (a : ℤ) = 2 * m * n := by linear_combination (norm := parley_norm) s52
  have s68 : ∃ m : ℕ, 0 < m ∧ (∃ n : ℕ, 0 < n ∧ ((((((n : ℤ) < (m : ℤ) ∧ (Int.gcd (m : ℤ) (n : ℤ) : ℤ) = 1) ∧ Odd ((m : ℤ) + (n : ℤ))) ∧ (a : ℤ) = 2 * (m : ℤ) * (n : ℤ)) ∧ (b : ℤ) = (m : ℤ) ^ 2 - (n : ℤ) ^ 2) ∧ (c : ℤ) = (m : ℤ) ^ 2 + (n : ℤ) ^ 2)) := ⟨m.toNat, by (try simp only [parley_cast_toNat (show (0 : ℤ) ≤ m by parley_side)]); (try push_cast); parley_side, n.toNat, by (try simp only [parley_cast_toNat (show (0 : ℤ) ≤ m by parley_side)]); (try push_cast); (try simp only [parley_cast_toNat (show (0 : ℤ) ≤ n by parley_side)]); (try push_cast); parley_side, ⟨⟨⟨⟨⟨by (try simp only [parley_cast_toNat (show (0 : ℤ) ≤ m by parley_side)]); (try push_cast); (try simp only [parley_cast_toNat (show (0 : ℤ) ≤ n by parley_side)]); (try push_cast); parley_side, by (try simp only [parley_cast_toNat (show (0 : ℤ) ≤ m by parley_side)]); (try push_cast); (try simp only [parley_cast_toNat (show (0 : ℤ) ≤ n by parley_side)]); (try push_cast); parley_side⟩, by (try simp only [parley_cast_toNat (show (0 : ℤ) ≤ m by parley_side)]); (try push_cast); (try simp only [parley_cast_toNat (show (0 : ℤ) ≤ n by parley_side)]); (try push_cast); parley_side⟩, by (try simp only [parley_cast_toNat (show (0 : ℤ) ≤ m by parley_side)]); (try push_cast); (try simp only [parley_cast_toNat (show (0 : ℤ) ≤ n by parley_side)]); (try push_cast); parley_side⟩, by (try simp only [parley_cast_toNat (show (0 : ℤ) ≤ m by parley_side)]); (try push_cast); (try simp only [parley_cast_toNat (show (0 : ℤ) ≤ n by parley_side)]); (try push_cast); parley_side⟩, by (try simp only [parley_cast_toNat (show (0 : ℤ) ≤ m by parley_side)]); (try push_cast); (try simp only [parley_cast_toNat (show (0 : ℤ) ≤ n by parley_side)]); (try push_cast); parley_side⟩⟩
  all_goals exact s68

end Parley.Proofs.Wiedijk.PythagoreanTriples.PrimitiveTriple
