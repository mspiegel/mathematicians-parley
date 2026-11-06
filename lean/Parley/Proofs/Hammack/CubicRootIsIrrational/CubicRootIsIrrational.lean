module

public import AlgebraTactics
public import ArithTactics
public import SubstTactics
public import Tactics
public import Batteries.Tactic.Init
public import Mathlib.Algebra.Group.Even
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Rat.Init
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Qify
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Numbers
public import Parley.Proofs.Wiedijk.Sqrt2Irrational.LowestTerms

/-! Written from proofs/hammack/cubic-root-is-irrational.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.CubicRootIsIrrational.CubicRootIsIrrational

set_option maxHeartbeats 800000 in
theorem cubic_root_is_irrational (x : ℝ) (hH2 : x ^ 3 + x + 3 = 0) :
    Irrational x := by
  -- 1. contradiction
  have s1 : ¬ (∃ m : ℚ, (m : ℝ) = x) := by
    by_contra hc_hS
    have hS : ∃ m : ℚ, (m : ℝ) = x := by parley_suppose hc_hS
    -- 1.1. obtain p, q: thm:lowest-terms, from S
    obtain ⟨p, q, ⟨⟨s1_1a, s1_1b⟩, s1_1c⟩⟩ := (Parley.Proofs.Wiedijk.Sqrt2Irrational.LowestTerms.lowest_terms (x := (Classical.choose hS)))
    have s1_1b : x = (p : ℝ) / (q : ℝ) := by rw [← Classical.choose_spec hS]; exact_mod_cast s1_1b
    -- 1.2. substitute x = p/q (line 1.1) into H2
    have s1_2 : ((p : ℚ) / (q : ℚ)) ^ 3 + (p : ℚ) / (q : ℚ) + 3 = 0 := by parley_subst_at s1_1b hH2
    -- 1.3. algebra, from 1.2
    have r29_1 : q ≠ 0 := by parley_side
    have s1_3 : p ^ 3 + p * q ^ 2 + 3 * q ^ 3 = 0 := by qify at *; linear_combination (norm := parley_field) ((q : ℚ) ^ 3) * s1_2
    -- 1.4. mun:even-or-odd n := p
    have s1_4 : Even p ∨ Odd p := by first | exact (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := p)) | exact ((Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := p))).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := p)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := p)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := p)); parley_side)
    -- 1.5. cases, from 1.4
    have s1_5 : Even (1 : ℤ) := by
      rcases s1_4 with hC1 | hC4
      · skip
        -- 1.5.1. obtain r: def:even n := p, from C1
        obtain ⟨r, s1_5_1⟩ := ((Parley.Items.Stdlib.Divisibility.def_even (n := p))).mp (by parley_side)
        -- 1.5.2. mun:even-or-odd n := q
        have s1_5_2 : Even q ∨ Odd q := by first | exact (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := q)) | exact ((Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := q))).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := q)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := q)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := q)); parley_side)
        -- 1.5.3. cases, from 1.5.2
        have s1_5_3 : Even (1 : ℤ) := by
          rcases s1_5_2 with hC2 | hC3
          · skip
            -- 1.5.3.1. obtain s: def:even n := q, from C2
            obtain ⟨s, s1_5_3_1⟩ := ((Parley.Items.Stdlib.Divisibility.def_even (n := q))).mp (by parley_side)
            -- 1.5.3.2. def:divides d := 2, n := p, from 1.5.1
            have s1_5_3_2 : (2 : ℤ) ∣ p := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_divides (d := (2 : ℤ)) (n := p))).mpr ⟨r, by parley_side⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (2 : ℤ)) (n := p))).mpr ⟨r, by parley_side⟩; parley_side)
            -- 1.5.3.3. def:divides d := 2, n := q, from 1.5.3.1
            have s1_5_3_3 : (2 : ℤ) ∣ q := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_divides (d := (2 : ℤ)) (n := q))).mpr ⟨s, by parley_side⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (2 : ℤ)) (n := q))).mpr ⟨s, by parley_side⟩; parley_side)
            -- 1.5.3.4. exhibit, from 1.5.3.2, 1.5.3.3
            have r63_1 : (2 : ℤ) > 1 := by parley_arith
            have s1_5_3_4 : ∃ d : ℤ, (d > 1 ∧ d ∣ p) ∧ d ∣ q := ⟨(2 : ℤ), ⟨⟨by parley_side, by parley_side⟩, by parley_side⟩⟩
            all_goals parley_side
          · skip
            -- 1.5.3.5. obtain s: def:odd n := q, from C3
            obtain ⟨s, s1_5_3_5⟩ := ((Parley.Items.Stdlib.Divisibility.def_odd (n := q))).mp (by parley_side)
            -- 1.5.3.6. substitute
            have s1_5_3_6 : (2 * r) ^ 3 + 2 * r * (2 * s + 1) ^ 2 + 3 * (2 * s + 1) ^ 3 = 0 := by
              have c1 : p = 2 * r := by parley_subst s1_5_1
              have row1 : (2 * r) ^ 3 + 2 * r * q ^ 2 + 3 * q ^ 3 = 0 := by parley_subst_at c1 s1_3
              have c2 : q = 2 * s + 1 := by parley_subst s1_5_3_5
              have row2 : (2 * r) ^ 3 + 2 * r * (2 * s + 1) ^ 2 + 3 * (2 * s + 1) ^ 3 = 0 := by parley_subst_at c2 row1
              exact row2
            -- 1.5.3.7. algebra, from 1.5.3.6
            have s1_5_3_7 : 1 = 2 * -(4 * r ^ 3 + 4 * r * s ^ 2 + 4 * r * s + r + 12 * s ^ 3 + 18 * s ^ 2 + 9 * s + 1) := by linear_combination (norm := parley_norm) s1_5_3_6
            -- 1.5.3.8. def:even n := 1, from 1.5.3.7
            have s1_5_3_8 : Even (1 : ℤ) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_even (n := (1 : ℤ)))).mpr ⟨-(4 * r ^ 3 + 4 * r * s ^ 2 + 4 * r * s + r + 12 * s ^ 3 + 18 * s ^ 2 + 9 * s + 1), by parley_side⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_even (n := (1 : ℤ)))).mpr ⟨-(4 * r ^ 3 + 4 * r * s ^ 2 + 4 * r * s + r + 12 * s ^ 3 + 18 * s ^ 2 + 9 * s + 1), by parley_side⟩; parley_side)
            all_goals parley_side
        all_goals parley_side
      · skip
        -- 1.5.4. obtain r: def:odd n := p, from C4
        obtain ⟨r, s1_5_4⟩ := ((Parley.Items.Stdlib.Divisibility.def_odd (n := p))).mp (by parley_side)
        -- 1.5.5. substitute p = 2r + 1 (line 1.5.4) into line 1.3
        have s1_5_5 : (2 * r + 1) ^ 3 + (2 * r + 1) * q ^ 2 + 3 * q ^ 3 = 0 := by parley_subst_at s1_5_4 s1_3
        -- 1.5.6. mun:even-or-odd n := q
        have s1_5_6 : Even q ∨ Odd q := by first | exact (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := q)) | exact ((Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := q))).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := q)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := q)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := q)); parley_side)
        -- 1.5.7. cases, from 1.5.6
        have s1_5_7 : Even (1 : ℤ) := by
          rcases s1_5_6 with hC5 | hC6
          · skip
            -- 1.5.7.1. obtain s: def:even n := q, from C5
            obtain ⟨s, s1_5_7_1⟩ := ((Parley.Items.Stdlib.Divisibility.def_even (n := q))).mp (by parley_side)
            -- 1.5.7.2. substitute q = 2s (line 1.5.7.1) into line 1.5.5
            have s1_5_7_2 : (2 * r + 1) ^ 3 + (2 * r + 1) * (2 * s) ^ 2 + 3 * (2 * s) ^ 3 = 0 := by parley_subst_at s1_5_7_1 s1_5_5
            -- 1.5.7.3. algebra, from 1.5.7.2
            have s1_5_7_3 : 1 = 2 * -(4 * r ^ 3 + 6 * r ^ 2 + 3 * r + 4 * r * s ^ 2 + 2 * s ^ 2 + 12 * s ^ 3) := by linear_combination (norm := parley_norm) s1_5_7_2
            -- 1.5.7.4. def:even n := 1, from 1.5.7.3
            have s1_5_7_4 : Even (1 : ℤ) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_even (n := (1 : ℤ)))).mpr ⟨-(4 * r ^ 3 + 6 * r ^ 2 + 3 * r + 4 * r * s ^ 2 + 2 * s ^ 2 + 12 * s ^ 3), by parley_side⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_even (n := (1 : ℤ)))).mpr ⟨-(4 * r ^ 3 + 6 * r ^ 2 + 3 * r + 4 * r * s ^ 2 + 2 * s ^ 2 + 12 * s ^ 3), by parley_side⟩; parley_side)
            all_goals parley_side
          · skip
            -- 1.5.7.5. obtain s: def:odd n := q, from C6
            obtain ⟨s, s1_5_7_5⟩ := ((Parley.Items.Stdlib.Divisibility.def_odd (n := q))).mp (by parley_side)
            -- 1.5.7.6. substitute q = 2s + 1 (line 1.5.7.5) into line 1.5.5
            have s1_5_7_6 : (2 * r + 1) ^ 3 + (2 * r + 1) * (2 * s + 1) ^ 2 + 3 * (2 * s + 1) ^ 3 = 0 := by parley_subst_at s1_5_7_5 s1_5_5
            -- 1.5.7.7. algebra, from 1.5.7.6
            have s1_5_7_7 : 1 = 2 * -(4 * r ^ 3 + 6 * r ^ 2 + 4 * r + 4 * r * s ^ 2 + 4 * r * s + 12 * s ^ 3 + 20 * s ^ 2 + 11 * s + 2) := by linear_combination (norm := parley_norm) s1_5_7_6
            -- 1.5.7.8. def:even n := 1, from 1.5.7.7
            have s1_5_7_8 : Even (1 : ℤ) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_even (n := (1 : ℤ)))).mpr ⟨-(4 * r ^ 3 + 6 * r ^ 2 + 4 * r + 4 * r * s ^ 2 + 4 * r * s + 12 * s ^ 3 + 20 * s ^ 2 + 11 * s + 2), by parley_side⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_even (n := (1 : ℤ)))).mpr ⟨-(4 * r ^ 3 + 6 * r ^ 2 + 4 * r + 4 * r * s ^ 2 + 4 * r * s + 12 * s ^ 3 + 20 * s ^ 2 + 11 * s + 2), by parley_side⟩; parley_side)
            all_goals parley_side
        all_goals parley_side
    -- 1.6. mun:not-both n := 1, from 1.5
    have s1_6 : ¬ Odd (1 : ℤ) := by first | exact (Parley.Items.Stdlib.Divisibility.mun_not_both (n := (1 : ℤ)) s1_5) | exact ((Parley.Items.Stdlib.Divisibility.mun_not_both (n := (1 : ℤ)) s1_5)).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_not_both (n := (1 : ℤ)) s1_5) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_not_both (n := (1 : ℤ)) s1_5) | (have h := (Parley.Items.Stdlib.Divisibility.mun_not_both (n := (1 : ℤ)) s1_5); parley_side)
    -- 1.7. arithmetic
    have s1_7 : Odd (1 : ℤ) := by parley_arith
    all_goals parley_side
  -- 2. def:irrational, from 1
  have s2 : Irrational x := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Numbers.def_irrational (x := x))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Numbers.def_irrational (x := x))).mpr (by parley_side); parley_side)
  all_goals exact s2

end Parley.Proofs.Hammack.CubicRootIsIrrational.CubicRootIsIrrational
