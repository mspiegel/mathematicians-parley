module

public import ArithTactics
public import Tactics
public import Mathlib.Algebra.Group.Even
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
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

theorem three_prime :
    Nat.Prime (3 : ℤ).toNat := by
  -- 1. arithmetic
  have s1 : (3 : ℤ) > 1 := by parley_arith
  -- 2. proof
  have s2 : ∀ d : ℤ, 0 < d → d ∣ (3 : ℤ) → d = 1 ∨ d = 3 := by
    intro d hK
    intro hH
    -- 2.1. mun:divides-le e := d, m := 3, from H
    have s2_1 : d ≤ 3 := by exact (Parley.Items.Stdlib.Divisibility.mun_divides_le (e := d) hK (m := (3 : ℤ)) (by norm_num) hH)
    -- 2.2. inequalities, from K
    have s2_2 : 1 ≤ d := by linarith only [hK]
    -- 2.3. mun:le-cases x := 1, y := d, from 2.2
    have s2_3 : 1 < d ∨ 1 = d := by exact ((Parley.Items.Stdlib.Numbers.mun_le_cases (x := (1 : ℤ)) (y := d))).mp s2_2
    -- 2.4. cases, from 2.3
    rcases s2_3 with hC1 | hC2
    · skip
      -- 2.4.1. mun:integer-step m := 1, n := d, from C1
      have s2_4_1 : 1 + 1 ≤ d := by exact (Parley.Items.Stdlib.Numbers.mun_integer_step (m := (1 : ℤ)) (n := d) hC1)
      -- 2.4.2. inequalities, from 2.4.1
      have s2_4_2 : 2 ≤ d := by linarith only [s2_4_1]
      -- 2.4.3. mun:le-cases x := 2, y := d, from 2.4.2
      have s2_4_3 : 2 < d ∨ 2 = d := by exact ((Parley.Items.Stdlib.Numbers.mun_le_cases (x := (2 : ℤ)) (y := d))).mp s2_4_2
      -- 2.4.4. cases, from 2.4.3
      rcases s2_4_3 with hC3 | hC4
      · skip
        -- 2.4.4.1. mun:integer-step m := 2, n := d, from C3
        have s2_4_4_1 : 2 + 1 ≤ d := by exact (Parley.Items.Stdlib.Numbers.mun_integer_step (m := (2 : ℤ)) (n := d) hC3)
        -- 2.4.4.2. inequalities, from 2.4.4.1
        have s2_4_4_2 : 3 ≤ d := by linarith only [s2_4_4_1]
        -- 2.4.4.3. antisymmetry, from 2.1, 2.4.4.2
        have s2_4_4_3 : d = 3 := le_antisymm s2_1 s2_4_4_2
        -- 2.4.4.4. mun:or-right, from 2.4.4.3
        exact (Parley.Items.Stdlib.Reasoning.mun_or_right (P := d = 1) (Q := d = 3) s2_4_4_3)
      · skip
        -- 2.4.4.5. substitute d = 2 (C4) into H
        have s2_4_4_5 : (2 : ℤ) ∣ (3 : ℤ) := by (have h := Eq.subst (motive := (fun t : ℤ => t ∣ (3 : ℤ))) hC4.symm hH; push_cast at h ⊢; all_goals exact_mod_cast h)
        -- 2.4.4.6. obtain k: def:divides d := 2, n := 3, from 2.4.4.5
        obtain ⟨k, s2_4_4_6⟩ := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (2 : ℤ)) (n := (3 : ℤ)))).mp s2_4_4_5
        -- 2.4.4.7. def:even n := 3, from 2.4.4.6
        have s2_4_4_7 : Even (3 : ℤ) := ((Parley.Items.Stdlib.Divisibility.def_even (n := (3 : ℤ)))).mpr ⟨k, s2_4_4_6⟩
        -- 2.4.4.8. arithmetic
        have s2_4_4_8 : (3 : ℤ) = 2 * 1 + 1 := by parley_arith
        -- 2.4.4.9. def:odd n := 3, from 2.4.4.8
        have s2_4_4_9 : Odd (3 : ℤ) := ((Parley.Items.Stdlib.Divisibility.def_odd (n := (3 : ℤ)))).mpr ⟨(1 : ℤ), by norm_num⟩
        -- 2.4.4.10. mun:not-both n := 3, from 2.4.4.7
        have s2_4_4_10 : ¬ Odd (3 : ℤ) := by exact (Parley.Items.Stdlib.Divisibility.mun_not_both (n := (3 : ℤ)) s2_4_4_7)
        exact absurd s2_4_4_9 s2_4_4_10
    · skip
      -- 2.4.5. mun:or-left, from C2
      exact (Parley.Items.Stdlib.Reasoning.mun_or_left (P := d = 1) (Q := d = 3) hC2.symm)
  -- 3. def:prime p := 3, from 1, 2
  exact ((Parley.Items.Stdlib.Divisibility.def_prime (p := (3 : ℤ)) (by norm_num))).mpr ⟨by norm_num, s2⟩

end Parley.Proofs.Hammack.Sqrt3Irrational.ThreePrime
