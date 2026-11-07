module

public import ArithTactics
public import OrderTactics
public import SubstTactics
public import Tactics
public import Mathlib.Algebra.Group.Even
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Reasoning

/-! Written from proofs/hammack/sqrt3-irrational.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.Sqrt3Irrational.ThreePrime

set_option maxHeartbeats 600000 in
theorem three_prime :
    Nat.Prime (3 : ℤ).toNat := by
  -- 1. arithmetic
  have s1 : (3 : ℤ) > 1 := by parley_arith
  -- 2. proof
  have s2 : ∀ d : ℤ, 0 < d → d ∣ (3 : ℤ) → d = 1 ∨ d = 3 := by
    intro d hK
    intro hH
    -- 2.1. mun:divides-le e := d, m := 3, from H
    have s2_1 : d ≤ 3 := by first | linarith [(Parley.Items.Stdlib.Divisibility.mun_divides_le (e := d) (by parley_side) (m := (3 : ℤ)) (by parley_side) hH)] | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_le (e := d) (by parley_side) (m := (3 : ℤ)) (by parley_side) hH); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_divides_le (e := d) (by parley_side) (m := (3 : ℤ)) (by parley_side) hH) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_le (e := d) (by parley_side) (m := (3 : ℤ)) (by parley_side) hH); parley_side)
    -- 2.2. inequalities, from K
    have s2_2 : 1 ≤ d := by parley_order
    -- 2.3. mun:le-cases x := 1, y := d, from 2.2
    have s2_3 : 1 < d ∨ 1 = d := by first | exact ((Parley.Items.Stdlib.Numbers.mun_le_cases (x := (1 : ℤ)) (y := d))).mp (by parley_side) | exact (((Parley.Items.Stdlib.Numbers.mun_le_cases (x := (1 : ℤ)) (y := d))).mp (by parley_side)).symm | simpa using ((Parley.Items.Stdlib.Numbers.mun_le_cases (x := (1 : ℤ)) (y := d))).mp (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_le_cases (x := (1 : ℤ)) (y := d))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_le_cases (x := (1 : ℤ)) (y := d))).mp (by parley_side); parley_side)
    -- 2.4. cases, from 2.3
    have s2_4 : d = 1 ∨ d = 3 := by
      rcases s2_3 with hC1 | hC2
      · skip
        -- 2.4.1. mun:integer-step m := 1, n := d, from C1
        have s2_4_1 : 1 + 1 ≤ d := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_integer_step (m := (1 : ℤ)) (n := d) hC1)] | (have h := (Parley.Items.Stdlib.Numbers.mun_integer_step (m := (1 : ℤ)) (n := d) hC1); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_integer_step (m := (1 : ℤ)) (n := d) hC1) | (have h := (Parley.Items.Stdlib.Numbers.mun_integer_step (m := (1 : ℤ)) (n := d) hC1); parley_side)
        -- 2.4.2. inequalities, from 2.4.1
        have s2_4_2 : 2 ≤ d := by parley_order
        -- 2.4.3. mun:le-cases x := 2, y := d, from 2.4.2
        have s2_4_3 : 2 < d ∨ 2 = d := by first | exact ((Parley.Items.Stdlib.Numbers.mun_le_cases (x := (2 : ℤ)) (y := d))).mp (by parley_side) | exact (((Parley.Items.Stdlib.Numbers.mun_le_cases (x := (2 : ℤ)) (y := d))).mp (by parley_side)).symm | simpa using ((Parley.Items.Stdlib.Numbers.mun_le_cases (x := (2 : ℤ)) (y := d))).mp (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_le_cases (x := (2 : ℤ)) (y := d))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_le_cases (x := (2 : ℤ)) (y := d))).mp (by parley_side); parley_side)
        -- 2.4.4. cases, from 2.4.3
        have s2_4_4 : d = 1 ∨ d = 3 := by
          rcases s2_4_3 with hC3 | hC4
          · skip
            -- 2.4.4.1. mun:integer-step m := 2, n := d, from C3
            have s2_4_4_1 : 2 + 1 ≤ d := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_integer_step (m := (2 : ℤ)) (n := d) hC3)] | (have h := (Parley.Items.Stdlib.Numbers.mun_integer_step (m := (2 : ℤ)) (n := d) hC3); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_integer_step (m := (2 : ℤ)) (n := d) hC3) | (have h := (Parley.Items.Stdlib.Numbers.mun_integer_step (m := (2 : ℤ)) (n := d) hC3); parley_side)
            -- 2.4.4.2. inequalities, from 2.4.4.1
            have s2_4_4_2 : 3 ≤ d := by parley_order
            -- 2.4.4.3. antisymmetry, from 2.1, 2.4.4.2
            have s2_4_4_3 : d = 3 := by parley_side
            -- 2.4.4.4. mun:or-right, from 2.4.4.3
            have s2_4_4_4 : d = 1 ∨ d = 3 := by exact (Parley.Items.Stdlib.Reasoning.mun_or_right (P := d = 1) (Q := d = 3) s2_4_4_3)
            all_goals parley_side
          · skip
            -- 2.4.4.5. substitute d = 2 (C4) into H
            have s2_4_4_5 : (2 : ℤ) ∣ (3 : ℤ) := by parley_subst_at hC4 hH
            -- 2.4.4.6. obtain k: def:divides d := 2, n := 3, from 2.4.4.5
            obtain ⟨k, s2_4_4_6⟩ := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (2 : ℤ)) (n := (3 : ℤ)))).mp (by parley_side)
            -- 2.4.4.7. def:even n := 3, from 2.4.4.6
            have s2_4_4_7 : Even (3 : ℤ) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_even (n := (3 : ℤ)))).mpr ⟨k, by parley_side⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_even (n := (3 : ℤ)))).mpr ⟨k, by parley_side⟩; parley_side)
            -- 2.4.4.8. arithmetic
            have s2_4_4_8 : (3 : ℤ) = 2 * 1 + 1 := by parley_arith
            -- 2.4.4.9. def:odd n := 3, from 2.4.4.8
            have s2_4_4_9 : Odd (3 : ℤ) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_odd (n := (3 : ℤ)))).mpr ⟨(1 : ℤ), by parley_side⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_odd (n := (3 : ℤ)))).mpr ⟨(1 : ℤ), by parley_side⟩; parley_side)
            -- 2.4.4.10. mun:not-both n := 3, from 2.4.4.7
            have s2_4_4_10 : ¬ Odd (3 : ℤ) := by exact (Parley.Items.Stdlib.Divisibility.mun_not_both (n := (3 : ℤ)) s2_4_4_7)
            all_goals parley_side
        all_goals parley_side
      · skip
        -- 2.4.5. mun:or-left, from C2
        have s2_4_5 : d = 1 ∨ d = 3 := by exact (Parley.Items.Stdlib.Reasoning.mun_or_left (P := d = 1) (Q := d = 3) (by parley_side))
        all_goals parley_side
    all_goals parley_side
  -- 3. def:prime p := 3, from 1, 2
  have s3 : Nat.Prime (3 : ℤ).toNat := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_prime (p := (3 : ℤ)) (by parley_side))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Divisibility.def_prime (p := (3 : ℤ)) (by parley_side))).mpr (by parley_side); parley_side)
  all_goals exact s3

end Parley.Proofs.Hammack.Sqrt3Irrational.ThreePrime
