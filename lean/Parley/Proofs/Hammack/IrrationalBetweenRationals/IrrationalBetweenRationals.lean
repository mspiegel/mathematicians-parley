module

public import AlgebraTactics
public import ArithTactics
public import NormTactics
public import OrderTactics
public import PowerTactics
public import RealTactics
public import SubstTactics
public import Tactics
public import Batteries.Classes.RatCast
public import Batteries.Tactic.Init
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Rat.Init
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Set
public import Parley.Items.Stdlib.Numbers
public import Parley.Proofs.Wiedijk.Sqrt2Irrational.Sqrt2Irrational

/-! Written from proofs/hammack/irrational-between-rationals.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.IrrationalBetweenRationals.IrrationalBetweenRationals

set_option maxHeartbeats 800000 in
theorem irrational_between_rationals (r : ℚ) (s : ℚ) (hH3 : r < s) :
    (∃ u : ℝ, (Irrational u ∧ (r : ℝ) < u) ∧ u < (s : ℝ)) := by
  -- 1. def:sqrt x := 2
  have r20_1 : (2 : ℤ) ≥ 0 := by parley_arith
  have s1a : Real.sqrt (2 : ℝ) ≥ 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := (2 : ℝ)) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := (2 : ℝ)) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := (2 : ℝ)) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := (2 : ℝ)) (by parley_side)); parley_side)
  have s1b : Real.sqrt (2 : ℝ) ^ 2 = 2 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := (2 : ℝ)) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := (2 : ℝ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := (2 : ℝ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := (2 : ℝ)) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := (2 : ℝ)) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := (2 : ℝ)) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := (2 : ℝ)) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := (2 : ℝ)) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := (2 : ℝ)) (by parley_side)); parley_rat_of_real h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := (2 : ℝ)) (by parley_side)); parley_side)
  -- 2. thm:sqrt2-irrational
  have s2 : Irrational (Real.sqrt (2 : ℝ)) := by exact Parley.Proofs.Wiedijk.Sqrt2Irrational.Sqrt2Irrational.sqrt2_irrational
  -- 3. calculation
  have s3 : 0 ^ 2 < Real.sqrt (2 : ℝ) ^ 2 := by
    calc (0 ^ 2 : ℝ) = 0 := by norm_num
      _ < 2 := by norm_num
      _ = Real.sqrt (2 : ℝ) ^ 2 := by parley_side
  -- 4. mun:square-less x := 0, y := √2, from 1, 3
  have r33_1 : (0 : ℤ) ≥ 0 := by parley_arith
  have s4 : 0 < Real.sqrt (2 : ℝ) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Numbers.mun_square_less (x := (0 : ℝ)) (y := Real.sqrt (2 : ℝ)) (by parley_side) (by parley_side))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_square_less (x := (0 : ℝ)) (y := Real.sqrt (2 : ℝ)) (by parley_side) (by parley_side))).mpr (by parley_side); parley_side)
  -- 5. calculation
  have s5 : Real.sqrt (2 : ℝ) ^ 2 < 2 ^ 2 := by
    calc Real.sqrt (2 : ℝ) ^ 2 = 2 := by parley_side
      _ < 2 ^ 2 := by norm_num
  -- 6. mun:square-less x := √2, y := 2, from 1, 5
  have r42_1 : (2 : ℤ) ≥ 0 := by parley_arith
  have s6 : Real.sqrt (2 : ℝ) < 2 := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Numbers.mun_square_less (x := Real.sqrt (2 : ℝ)) (y := (2 : ℝ)) (by parley_side) (by parley_side))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_square_less (x := Real.sqrt (2 : ℝ)) (y := (2 : ℝ)) (by parley_side) (by parley_side))).mpr (by parley_side); parley_side)
  -- 7. mun:product-positive x := 1/2, y := √2, from 4
  have r46_1 : (1 / 2 : ℚ) > 0 := by parley_arith
  have s7 : 0 < 1 / 2 * Real.sqrt (2 : ℝ) := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_product_positive (x := (1 / 2 : ℝ)) (y := Real.sqrt (2 : ℝ)) (by parley_side) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_product_positive (x := (1 / 2 : ℝ)) (y := Real.sqrt (2 : ℝ)) (by parley_side) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_product_positive (x := (1 / 2 : ℝ)) (y := Real.sqrt (2 : ℝ)) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_product_positive (x := (1 / 2 : ℝ)) (y := Real.sqrt (2 : ℝ)) (by parley_side) (by parley_side)); parley_side)
  -- 8. calculation
  have r50_1 : (1 / 2 : ℚ) > 0 := by parley_arith
  have s8 : 1 / 2 * Real.sqrt (2 : ℝ) < 1 := by
    calc 1 / 2 * Real.sqrt (2 : ℝ) < 1 / 2 * 2 := by first | linarith [((Parley.Items.Stdlib.Numbers.mun_less_scaled (x := Real.sqrt (2 : ℝ)) (y := (2 : ℝ)) (c := (1 / 2 : ℝ)) (by parley_side))).mp (by parley_side)] | (have h := ((Parley.Items.Stdlib.Numbers.mun_less_scaled (x := Real.sqrt (2 : ℝ)) (y := (2 : ℝ)) (c := (1 / 2 : ℝ)) (by parley_side))).mp (by parley_side); push_cast at h; linarith) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_less_scaled (x := Real.sqrt (2 : ℝ)) (y := (2 : ℝ)) (c := (1 / 2 : ℝ)) (by parley_side))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_less_scaled (x := Real.sqrt (2 : ℝ)) (y := (2 : ℝ)) (c := (1 / 2 : ℝ)) (by parley_side))).mp (by parley_side); parley_side)
      _ = 1 := by norm_num
  -- 9. inequalities
  have s9 : 0 < s - r := by parley_order
  set u : ℝ := (r : ℝ) + ((s : ℝ) - (r : ℝ)) * (1 / 2 * Real.sqrt (2 : ℝ)) with hD1
  have hD1_kind : True := by parley_side
  -- 10. mun:product-positive x := s − r, y := (1/2)·√2, from 7, 9
  have s10 : ((s : ℝ) - (r : ℝ)) * (1 / 2 * Real.sqrt (2 : ℝ)) > 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_product_positive (x := (s : ℝ) - (r : ℝ)) (y := 1 / 2 * Real.sqrt (2 : ℝ)) (by parley_side) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_product_positive (x := (s : ℝ) - (r : ℝ)) (y := 1 / 2 * Real.sqrt (2 : ℝ)) (by parley_side) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_product_positive (x := (s : ℝ) - (r : ℝ)) (y := 1 / 2 * Real.sqrt (2 : ℝ)) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_product_positive (x := (s : ℝ) - (r : ℝ)) (y := 1 / 2 * Real.sqrt (2 : ℝ)) (by parley_side) (by parley_side)); parley_side)
  -- 11. inequalities
  have s11 : (r : ℝ) + ((s : ℝ) - (r : ℝ)) * (1 / 2 * Real.sqrt (2 : ℝ)) > (r : ℝ) := by parley_order
  -- 12. transitivity, from 11, D1
  have s12 : (r : ℝ) < u := by parley_order
  -- 13. mun:less-scaled x := (1/2)·√2, y := 1, c := s − r, from 8, 9
  have s13 : ((s : ℝ) - (r : ℝ)) * (1 / 2 * Real.sqrt (2 : ℝ)) < ((s : ℝ) - (r : ℝ)) * 1 := by first | linarith [((Parley.Items.Stdlib.Numbers.mun_less_scaled (x := 1 / 2 * Real.sqrt (2 : ℝ)) (y := (1 : ℝ)) (c := (s : ℝ) - (r : ℝ)) (by parley_side))).mp (by parley_side)] | (have h := ((Parley.Items.Stdlib.Numbers.mun_less_scaled (x := 1 / 2 * Real.sqrt (2 : ℝ)) (y := (1 : ℝ)) (c := (s : ℝ) - (r : ℝ)) (by parley_side))).mp (by parley_side); push_cast at h; linarith) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_less_scaled (x := 1 / 2 * Real.sqrt (2 : ℝ)) (y := (1 : ℝ)) (c := (s : ℝ) - (r : ℝ)) (by parley_side))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_less_scaled (x := 1 / 2 * Real.sqrt (2 : ℝ)) (y := (1 : ℝ)) (c := (s : ℝ) - (r : ℝ)) (by parley_side))).mp (by parley_side); parley_side)
  -- 14. inequalities
  have s14 : (r : ℝ) + ((s : ℝ) - (r : ℝ)) * (1 / 2 * Real.sqrt (2 : ℝ)) < (r : ℝ) + ((s : ℝ) - (r : ℝ)) := by parley_order
  -- 15. algebra
  have s15 : r + (s - r) = s := by parley_ring
  -- 16. transitivity, from D1, 14, 15
  have s16 : u < (s : ℝ) := by parley_order
  -- 17. contradiction
  have s17 : ¬ (∃ m : ℚ, (m : ℝ) = u) := by
    by_contra hc_hS
    have hS : ∃ m : ℚ, (m : ℝ) = u := by parley_suppose hc_hS
    -- 17.1. obtain a, b: def:rational x := u, from S
    obtain ⟨a, b, s17_1a, s17_1b⟩ := ((Parley.Items.Stdlib.Numbers.def_rational (x := u))).mp (by parley_side)
    -- 17.2. obtain p, q: def:rational x := r
    obtain ⟨p, q, s17_2a, s17_2b⟩ := ((Parley.Items.Stdlib.Numbers.def_rational (x := r))).mp (by parley_side)
    -- 17.3. obtain c, d: def:rational x := s
    obtain ⟨c, d, s17_3a, s17_3b⟩ := ((Parley.Items.Stdlib.Numbers.def_rational (x := s))).mp (by parley_side)
    -- 17.4. substitute s = c/d (line 17.3)
    have s17_4 : s - r = (c : ℚ) / (d : ℚ) - r := by parley_subst s17_3b
    -- 17.5. substitute r = p/q (line 17.2)
    have s17_5 : (c : ℚ) / (d : ℚ) - r = (c : ℚ) / (d : ℚ) - (p : ℚ) / (q : ℚ) := by parley_subst s17_2b
    -- 17.6. transitivity, from 17.4, 17.5
    have s17_6 : s - r = (c : ℚ) / (d : ℚ) - (p : ℚ) / (q : ℚ) := by parley_side
    -- 17.7. mun:product-positive x := q, y := d, from 17.2, 17.3
    have s17_7 : q * d > 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_product_positive (x := q) (y := d) (by parley_side) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_product_positive (x := q) (y := d) (by parley_side) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_product_positive (x := q) (y := d) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_product_positive (x := q) (y := d) (by parley_side) (by parley_side)); parley_side)
    -- 17.8. mun:product-positive x := s − r, y := q·d, from 9, 17.7
    have s17_8 : (s - r) * ((q : ℚ) * (d : ℚ)) > 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_product_positive (x := s - r) (y := (q : ℚ) * (d : ℚ)) (by parley_side) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_product_positive (x := s - r) (y := (q : ℚ) * (d : ℚ)) (by parley_side) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_product_positive (x := s - r) (y := (q : ℚ) * (d : ℚ)) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_product_positive (x := s - r) (y := (q : ℚ) * (d : ℚ)) (by parley_side) (by parley_side)); parley_side)
    -- 17.9. substitute s − r = c/d − p/q (line 17.6) into line 17.8
    have s17_9 : ((c : ℚ) / (d : ℚ) - (p : ℚ) / (q : ℚ)) * ((q : ℚ) * (d : ℚ)) > 0 := by parley_subst_at s17_6 s17_8
    -- 17.10. algebra
    have s17_10 : ((c : ℚ) / (d : ℚ) - (p : ℚ) / (q : ℚ)) * ((q : ℚ) * (d : ℚ)) = (c : ℚ) * (q : ℚ) - (p : ℚ) * (d : ℚ) := by parley_ring
    -- 17.11. transitivity, from 17.9, 17.10
    have s17_11 : 0 < c * q - p * d := by parley_order
    have hD2_kind : 0 < c * q - p * d := by exact (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := c * q - p * d) s17_11)
    set m : ℤ := c * q - p * d with hD2
    have hD2_pos := hD2_kind
    -- 17.12. algebra, from D1
    have s17_12 : u - (r : ℝ) = ((s : ℝ) - (r : ℝ)) * (1 / 2 * Real.sqrt (2 : ℝ)) := by
      try simp only [hD1] at *
      try push_cast at *
      parley_ring
    -- 17.13. substitute
    have s17_13 : (a : ℝ) / (b : ℝ) - (p : ℝ) / (q : ℝ) = ((c : ℝ) / (d : ℝ) - (p : ℝ) / (q : ℝ)) * (1 / 2 * Real.sqrt (2 : ℝ)) := by
      have c1 : u = (a : ℝ) / (b : ℝ) := by parley_subst s17_1b
      have row1 : (a : ℝ) / (b : ℝ) - (r : ℝ) = ((s : ℝ) - (r : ℝ)) * (1 / 2 * Real.sqrt (2 : ℝ)) := by parley_subst_at c1 s17_12
      have c2 : r = (p : ℚ) / (q : ℚ) := by parley_subst s17_2b
      have c2_w : (r : ℝ) = (p : ℝ) / (q : ℝ) := by have h := congrArg (fun x : ℚ => (x : ℝ)) c2; push_cast at h; linear_combination (norm := parley_norm) h
      have row2 : (a : ℝ) / (b : ℝ) - (p : ℝ) / (q : ℝ) = ((s : ℝ) - (p : ℝ) / (q : ℝ)) * (1 / 2 * Real.sqrt (2 : ℝ)) := by first | parley_put_at c2_w row1 | parley_put_at c2 row1 | parley_subst_at c2_w row1 | parley_subst_at c2 row1
      have c3 : s = (c : ℚ) / (d : ℚ) := by parley_subst s17_3b
      have c3_w : (s : ℝ) = (c : ℝ) / (d : ℝ) := by have h := congrArg (fun x : ℚ => (x : ℝ)) c3; push_cast at h; linear_combination (norm := parley_norm) h
      have row3 : (a : ℝ) / (b : ℝ) - (p : ℝ) / (q : ℝ) = ((c : ℝ) / (d : ℝ) - (p : ℝ) / (q : ℝ)) * (1 / 2 * Real.sqrt (2 : ℝ)) := by first | parley_put_at c3_w row2 | parley_put_at c3 row2 | parley_subst_at c3_w row2 | parley_subst_at c3 row2
      exact row3
    -- 17.14. algebra, from 17.13
    have s17_14 : (b : ℝ) * ((c : ℝ) * (q : ℝ) - (p : ℝ) * (d : ℝ)) * Real.sqrt (2 : ℝ) = 2 * (d : ℝ) * ((a : ℝ) * (q : ℝ) - (p : ℝ) * (b : ℝ)) := by linear_combination (norm := parley_field) (-2 * (b : ℝ) * (d : ℝ) * (q : ℝ)) * s17_13
    -- 17.15. substitute c·q − p·d = m (D2) into line 17.14
    have s17_15 : (b : ℝ) * (m : ℝ) * Real.sqrt (2 : ℝ) = 2 * (d : ℝ) * ((a : ℝ) * (q : ℝ) - (p : ℝ) * (b : ℝ)) := by
      have hD2_w : (m : ℝ) = (c : ℝ) * (q : ℝ) - (p : ℝ) * (d : ℝ) := by have h := congrArg (fun x : ℤ => (x : ℝ)) hD2; push_cast at h; linear_combination (norm := parley_norm) h
      first | parley_subst_at hD2_w s17_14 | parley_subst_at hD2 s17_14
    -- 17.16. algebra, from 17.15
    have s17_16 : Real.sqrt (2 : ℝ) = 2 * (d : ℝ) * ((a : ℝ) * (q : ℝ) - (p : ℝ) * (b : ℝ)) / ((b : ℝ) * (m : ℝ)) := by linear_combination (norm := parley_field) ((1) / (((b : ℝ) * (m : ℝ)))) * s17_15
    -- 17.17. def:rational x := √2, from 17.16
    have s17_17 : ∃ m : ℚ, (m : ℝ) = Real.sqrt (2 : ℝ) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Numbers.def_rational (x := Real.sqrt (2 : ℝ)))).mpr ⟨2 * d * (a * q - p * b), b * m, by parley_side, by parley_side⟩ | (have h := ((Parley.Items.Stdlib.Numbers.def_rational (x := Real.sqrt (2 : ℝ)))).mpr ⟨2 * d * (a * q - p * b), b * m, by parley_side, by parley_side⟩; parley_side)
    -- 17.18. def:irrational x := √2, from 2
    have s17_18 : ¬ (∃ m : ℚ, (m : ℝ) = Real.sqrt (2 : ℝ)) := by first | exact (((Parley.Items.Stdlib.Numbers.def_irrational (x := Real.sqrt (2 : ℝ)))).mp (by parley_side)).2 | exact ((((Parley.Items.Stdlib.Numbers.def_irrational (x := Real.sqrt (2 : ℝ)))).mp (by parley_side)).2).symm | simpa using (((Parley.Items.Stdlib.Numbers.def_irrational (x := Real.sqrt (2 : ℝ)))).mp (by parley_side)).2 | exact_mod_cast (((Parley.Items.Stdlib.Numbers.def_irrational (x := Real.sqrt (2 : ℝ)))).mp (by parley_side)).2 | (have h := (((Parley.Items.Stdlib.Numbers.def_irrational (x := Real.sqrt (2 : ℝ)))).mp (by parley_side)).2; parley_rat_of_real h) | (have h := (((Parley.Items.Stdlib.Numbers.def_irrational (x := Real.sqrt (2 : ℝ)))).mp (by parley_side)).2; parley_side)
    all_goals parley_side
  -- 18. def:irrational x := u, from 17
  have s18 : Irrational u := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Numbers.def_irrational (x := u))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Numbers.def_irrational (x := u))).mpr (by parley_side); parley_side)
  -- 19. exhibit, from 12, 16, 18
  have s19 : ∃ u : ℝ, (Irrational u ∧ (r : ℝ) < u) ∧ u < (s : ℝ) := ⟨u, ⟨⟨by parley_side, by parley_side⟩, by parley_side⟩⟩
  all_goals exact s19

end Parley.Proofs.Hammack.IrrationalBetweenRationals.IrrationalBetweenRationals
