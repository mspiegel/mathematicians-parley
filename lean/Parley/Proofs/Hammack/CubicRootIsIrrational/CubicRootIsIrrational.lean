module

public import AlgebraTactics
public import ArithTactics
public import NormTactics
public import Tactics
public import Batteries.Classes.RatCast
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Even
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Rat.Init
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
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
    intro hS
    -- 1.1. obtain p, q: thm:lowest-terms, from S
    obtain ⟨p, q, ⟨⟨s1_1a, s1_1b⟩, s1_1c⟩⟩ := (Parley.Proofs.Wiedijk.Sqrt2Irrational.LowestTerms.lowest_terms (x := (Classical.choose hS)))
    have s1_1b : x = (p : ℝ) / (q : ℝ) := by rw [← Classical.choose_spec hS]; exact_mod_cast s1_1b
    -- 1.2. substitute x = p/q (line 1.1) into H2
    have s1_2 : ((p : ℚ) / (q : ℚ)) ^ 3 + (p : ℚ) / (q : ℚ) + 3 = 0 := by (have h := Eq.subst (motive := (fun t : ℝ => t ^ 3 + t + 3 = 0)) s1_1b hH2; push_cast at h ⊢; all_goals exact_mod_cast h)
    -- 1.3. algebra, from 1.2
    have r29_1 : q ≠ 0 := by parley_side
    have s1_3 : p ^ 3 + p * q ^ 2 + 3 * q ^ 3 = 0 := by qify at *; linear_combination (norm := parley_field) ((q : ℚ) ^ 3) * s1_2
    -- 1.4. mun:even-or-odd n := p
    have s1_4 : Even p ∨ Odd p := by exact (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := p))
    -- 1.5. cases, from 1.4
    have s1_5 : Even (1 : ℤ) := by
      rcases s1_4 with hC1 | hC4
      · skip
        -- 1.5.1. obtain r: def:even n := p, from C1
        obtain ⟨r, s1_5_1⟩ := ((Parley.Items.Stdlib.Divisibility.def_even (n := p))).mp hC1
        -- 1.5.2. mun:even-or-odd n := q
        have s1_5_2 : Even q ∨ Odd q := by exact (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := q))
        -- 1.5.3. cases, from 1.5.2
        rcases s1_5_2 with hC2 | hC3
        · skip
          -- 1.5.3.1. obtain s: def:even n := q, from C2
          obtain ⟨s, s1_5_3_1⟩ := ((Parley.Items.Stdlib.Divisibility.def_even (n := q))).mp hC2
          -- 1.5.3.2. def:divides d := 2, n := p, from 1.5.1
          have s1_5_3_2 : (2 : ℤ) ∣ p := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (2 : ℤ)) (n := p))).mpr ⟨r, s1_5_1⟩
          -- 1.5.3.3. def:divides d := 2, n := q, from 1.5.3.1
          have s1_5_3_3 : (2 : ℤ) ∣ q := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (2 : ℤ)) (n := q))).mpr ⟨s, s1_5_3_1⟩
          -- 1.5.3.4. exhibit, from 1.5.3.2, 1.5.3.3
          have r63_1 : (2 : ℤ) > 1 := by parley_arith
          have s1_5_3_4 : ∃ d : ℤ, (d > 1 ∧ d ∣ p) ∧ d ∣ q := ⟨(2 : ℤ), ⟨⟨r63_1, s1_5_3_2⟩, s1_5_3_3⟩⟩
          exact absurd s1_5_3_4 s1_1c
        · skip
          -- 1.5.3.5. obtain s: def:odd n := q, from C3
          obtain ⟨s, s1_5_3_5⟩ := ((Parley.Items.Stdlib.Divisibility.def_odd (n := q))).mp hC3
          -- 1.5.3.6. substitute
          have s1_5_3_6 : (2 * r) ^ 3 + 2 * r * (2 * s + 1) ^ 2 + 3 * (2 * s + 1) ^ 3 = 0 := by
            have c1 : p = 2 * r := by (have h := congrArg (fun t : ℤ => t) s1_5_1; push_cast at h ⊢; all_goals exact_mod_cast h)
            have row1 : (2 * r) ^ 3 + 2 * r * q ^ 2 + 3 * q ^ 3 = 0 := by (have h := Eq.subst (motive := (fun t : ℤ => t ^ 3 + t * q ^ 2 + 3 * q ^ 3 = 0)) c1 s1_3; push_cast at h ⊢; all_goals exact_mod_cast h)
            have c2 : q = 2 * s + 1 := by (have h := congrArg (fun t : ℤ => t) s1_5_3_5; push_cast at h ⊢; all_goals exact_mod_cast h)
            have row2 : (2 * r) ^ 3 + 2 * r * (2 * s + 1) ^ 2 + 3 * (2 * s + 1) ^ 3 = 0 := by (have h := Eq.subst (motive := (fun t : ℤ => (2 * r) ^ 3 + 2 * r * t ^ 2 + 3 * t ^ 3 = 0)) c2 row1; push_cast at h ⊢; all_goals exact_mod_cast h)
            exact row2
          -- 1.5.3.7. algebra, from 1.5.3.6
          have s1_5_3_7 : 1 = 2 * -(4 * r ^ 3 + 4 * r * s ^ 2 + 4 * r * s + r + 12 * s ^ 3 + 18 * s ^ 2 + 9 * s + 1) := by linear_combination (norm := parley_norm) s1_5_3_6
          -- 1.5.3.8. def:even n := 1, from 1.5.3.7
          exact ((Parley.Items.Stdlib.Divisibility.def_even (n := (1 : ℤ)))).mpr ⟨-(4 * r ^ 3 + 4 * r * s ^ 2 + 4 * r * s + r + 12 * s ^ 3 + 18 * s ^ 2 + 9 * s + 1), s1_5_3_7⟩
      · skip
        -- 1.5.4. obtain r: def:odd n := p, from C4
        obtain ⟨r, s1_5_4⟩ := ((Parley.Items.Stdlib.Divisibility.def_odd (n := p))).mp hC4
        -- 1.5.5. substitute p = 2r + 1 (line 1.5.4) into line 1.3
        have s1_5_5 : (2 * r + 1) ^ 3 + (2 * r + 1) * q ^ 2 + 3 * q ^ 3 = 0 := by (have h := Eq.subst (motive := (fun t : ℤ => t ^ 3 + t * q ^ 2 + 3 * q ^ 3 = 0)) s1_5_4 s1_3; push_cast at h ⊢; all_goals exact_mod_cast h)
        -- 1.5.6. mun:even-or-odd n := q
        have s1_5_6 : Even q ∨ Odd q := by exact (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := q))
        -- 1.5.7. cases, from 1.5.6
        rcases s1_5_6 with hC5 | hC6
        · skip
          -- 1.5.7.1. obtain s: def:even n := q, from C5
          obtain ⟨s, s1_5_7_1⟩ := ((Parley.Items.Stdlib.Divisibility.def_even (n := q))).mp hC5
          -- 1.5.7.2. substitute q = 2s (line 1.5.7.1) into line 1.5.5
          have s1_5_7_2 : (2 * r + 1) ^ 3 + (2 * r + 1) * (2 * s) ^ 2 + 3 * (2 * s) ^ 3 = 0 := by (have h := Eq.subst (motive := (fun t : ℤ => (2 * r + 1) ^ 3 + (2 * r + 1) * t ^ 2 + 3 * t ^ 3 = 0)) s1_5_7_1 s1_5_5; push_cast at h ⊢; all_goals exact_mod_cast h)
          -- 1.5.7.3. algebra, from 1.5.7.2
          have s1_5_7_3 : 1 = 2 * -(4 * r ^ 3 + 6 * r ^ 2 + 3 * r + 4 * r * s ^ 2 + 2 * s ^ 2 + 12 * s ^ 3) := by linear_combination (norm := parley_norm) s1_5_7_2
          -- 1.5.7.4. def:even n := 1, from 1.5.7.3
          exact ((Parley.Items.Stdlib.Divisibility.def_even (n := (1 : ℤ)))).mpr ⟨-(4 * r ^ 3 + 6 * r ^ 2 + 3 * r + 4 * r * s ^ 2 + 2 * s ^ 2 + 12 * s ^ 3), s1_5_7_3⟩
        · skip
          -- 1.5.7.5. obtain s: def:odd n := q, from C6
          obtain ⟨s, s1_5_7_5⟩ := ((Parley.Items.Stdlib.Divisibility.def_odd (n := q))).mp hC6
          -- 1.5.7.6. substitute q = 2s + 1 (line 1.5.7.5) into line 1.5.5
          have s1_5_7_6 : (2 * r + 1) ^ 3 + (2 * r + 1) * (2 * s + 1) ^ 2 + 3 * (2 * s + 1) ^ 3 = 0 := by (have h := Eq.subst (motive := (fun t : ℤ => (2 * r + 1) ^ 3 + (2 * r + 1) * t ^ 2 + 3 * t ^ 3 = 0)) s1_5_7_5 s1_5_5; push_cast at h ⊢; all_goals exact_mod_cast h)
          -- 1.5.7.7. algebra, from 1.5.7.6
          have s1_5_7_7 : 1 = 2 * -(4 * r ^ 3 + 6 * r ^ 2 + 4 * r + 4 * r * s ^ 2 + 4 * r * s + 12 * s ^ 3 + 20 * s ^ 2 + 11 * s + 2) := by linear_combination (norm := parley_norm) s1_5_7_6
          -- 1.5.7.8. def:even n := 1, from 1.5.7.7
          exact ((Parley.Items.Stdlib.Divisibility.def_even (n := (1 : ℤ)))).mpr ⟨-(4 * r ^ 3 + 6 * r ^ 2 + 4 * r + 4 * r * s ^ 2 + 4 * r * s + 12 * s ^ 3 + 20 * s ^ 2 + 11 * s + 2), s1_5_7_7⟩
    -- 1.6. mun:not-both n := 1, from 1.5
    have s1_6 : ¬ Odd (1 : ℤ) := by exact (Parley.Items.Stdlib.Divisibility.mun_not_both (n := (1 : ℤ)) s1_5)
    -- 1.7. arithmetic
    have s1_7 : Odd (1 : ℤ) := by parley_arith
    exact s1_6 s1_7
  -- 2. def:irrational, from 1
  exact ((Parley.Items.Stdlib.Numbers.def_irrational (x := x))).mpr (by parley_side)

end Parley.Proofs.Hammack.CubicRootIsIrrational.CubicRootIsIrrational
