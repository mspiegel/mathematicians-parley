module

public import AlgebraTactics
public import NormTactics
public import SetTactics
public import Tactics
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Set
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Sums
public import Parley.Proofs.Hammack.FiveConsecutiveDivisible.FiveConsecutiveNatural

/-! Written from proofs/hammack/five-consecutive-divisible.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.FiveConsecutiveDivisible.FiveConsecutiveDivisible

theorem five_consecutive_divisible (n : ℤ) :
    (120 : ℤ) ∣ n * (n + 1) * (n + 2) * (n + 3) * (n + 4) := by
  -- 1. mun:nonneg-or-neg x := n − 1
  have s1 : n - 1 ≥ 0 ∨ n - 1 < 0 := by exact (Parley.Items.Stdlib.Numbers.mun_nonneg_or_neg (x := n - 1))
  -- 2. cases, from 1
  rcases s1 with hC1 | hC2
  · skip
    -- 2.1. inequalities, from C1
    have s2_1 : 0 < n := by linarith only [hC1]
    -- 2.2. mun:pos-int-nat m := n, from 2.1
    have s2_2 : 0 < n := by exact (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := n) s2_1)
    -- 2.3. mun:nat-minus-one, from 2.2
    have s2_3 : 0 ≤ n - 1 := by exact (Parley.Items.Stdlib.Numbers.mun_nat_minus_one (n := n) s2_2)
    -- 2.4. thm:five-consecutive-natural m := n − 1, from 2.3
    have s2_4 : (120 : ℤ) ∣ (n - 1 + 1) * (n - 1 + 2) * (n - 1 + 3) * (n - 1 + 4) * (n - 1 + 5) := by exact (Parley.Proofs.Hammack.FiveConsecutiveDivisible.FiveConsecutiveNatural.five_consecutive_natural (m := n - 1) s2_3)
    -- 2.5. substitute
    have c1 : (n - 1 + 1) * (n - 1 + 2) * (n - 1 + 3) * (n - 1 + 4) * (n - 1 + 5) = n * (n + 1) * (n + 2) * (n + 3) * (n + 4) := by parley_ring
    have row1 : (120 : ℤ) ∣ n * (n + 1) * (n + 2) * (n + 3) * (n + 4) := by (have h := Eq.subst (motive := (fun t : ℤ => (120 : ℤ) ∣ t)) c1 s2_4; push_cast at h ⊢; all_goals exact_mod_cast h)
    exact row1
  · skip
    -- 2.6. mun:nonneg-or-neg x := n + 4
    have s2_6 : n + 4 ≥ 0 ∨ n + 4 < 0 := by exact (Parley.Items.Stdlib.Numbers.mun_nonneg_or_neg (x := n + 4))
    -- 2.7. cases, from 2.6
    rcases s2_6 with hC3 | hC9
    · skip
      -- 2.7.1. inequalities, from C2
      have s2_7_1 : n < 1 := by linarith only [hC2]
      -- 2.7.2. mun:integer-step m := n, n := 1, from 2.7.1
      have s2_7_2 : n + 1 ≤ 1 := by exact (Parley.Items.Stdlib.Numbers.mun_integer_step (m := n) (n := (1 : ℤ)) s2_7_1)
      -- 2.7.3. inequalities, from 2.7.2
      have s2_7_3 : n + 4 ≤ 4 := by linarith only [s2_7_2]
      -- 2.7.4. def:range-between k := n + 4, a := 0, b := 4, from C3, 2.7.3
      have s2_7_4 : n + 4 ∈ Finset.Icc (0 : ℤ) (4 : ℤ) := ((Parley.Items.Stdlib.Sums.def_range_between (k := n + 4) (a := (0 : ℤ)) (b := (4 : ℤ)))).mpr ⟨hC3, s2_7_3⟩
      -- 2.7.5. inspection, from 2.7.4
      have s2_7_5 : (((n + 4 = 0 ∨ n + 4 = 1) ∨ n + 4 = 2) ∨ n + 4 = 3) ∨ n + 4 = 4 := by (have h := s2_7_4; norm_num [Finset.mem_Icc, Set.mem_Icc] at h; norm_cast at h; omega)
      -- 2.7.6. cases, from 2.7.5
      rcases s2_7_5 with (((hC4 | hC5) | hC6) | hC7) | hC8
      · skip
        -- 2.7.6.1. algebra, from C4
        have s2_7_6_1 : n * (n + 1) * (n + 2) * (n + 3) * (n + 4) = 120 * 0 := by linear_combination (norm := parley_norm) (n ^ 4 + 6 * n ^ 3 + 11 * n ^ 2 + 6 * n) * hC4
        -- 2.7.6.2. def:divides d := 120, n := n·(n + 1)·(n + 2)·(n + 3)·(n + 4), from 2.7.6.1
        exact ((Parley.Items.Stdlib.Divisibility.def_divides (d := (120 : ℤ)) (n := n * (n + 1) * (n + 2) * (n + 3) * (n + 4)))).mpr ⟨(0 : ℤ), s2_7_6_1⟩
      · skip
        -- 2.7.6.3. algebra, from C5
        have s2_7_6_3 : n * (n + 1) * (n + 2) * (n + 3) * (n + 4) = 120 * 0 := by linear_combination (norm := parley_norm) (n ^ 4 + 7 * n ^ 3 + 14 * n ^ 2 + 8 * n) * hC5
        -- 2.7.6.4. def:divides d := 120, n := n·(n + 1)·(n + 2)·(n + 3)·(n + 4), from 2.7.6.3
        exact ((Parley.Items.Stdlib.Divisibility.def_divides (d := (120 : ℤ)) (n := n * (n + 1) * (n + 2) * (n + 3) * (n + 4)))).mpr ⟨(0 : ℤ), s2_7_6_3⟩
      · skip
        -- 2.7.6.5. algebra, from C6
        have s2_7_6_5 : n * (n + 1) * (n + 2) * (n + 3) * (n + 4) = 120 * 0 := by linear_combination (norm := parley_norm) (n ^ 4 + 8 * n ^ 3 + 19 * n ^ 2 + 12 * n) * hC6
        -- 2.7.6.6. def:divides d := 120, n := n·(n + 1)·(n + 2)·(n + 3)·(n + 4), from 2.7.6.5
        exact ((Parley.Items.Stdlib.Divisibility.def_divides (d := (120 : ℤ)) (n := n * (n + 1) * (n + 2) * (n + 3) * (n + 4)))).mpr ⟨(0 : ℤ), s2_7_6_5⟩
      · skip
        -- 2.7.6.7. algebra, from C7
        have s2_7_6_7 : n * (n + 1) * (n + 2) * (n + 3) * (n + 4) = 120 * 0 := by linear_combination (norm := parley_norm) (n ^ 4 + 9 * n ^ 3 + 26 * n ^ 2 + 24 * n) * hC7
        -- 2.7.6.8. def:divides d := 120, n := n·(n + 1)·(n + 2)·(n + 3)·(n + 4), from 2.7.6.7
        exact ((Parley.Items.Stdlib.Divisibility.def_divides (d := (120 : ℤ)) (n := n * (n + 1) * (n + 2) * (n + 3) * (n + 4)))).mpr ⟨(0 : ℤ), s2_7_6_7⟩
      · skip
        -- 2.7.6.9. algebra, from C8
        have s2_7_6_9 : n * (n + 1) * (n + 2) * (n + 3) * (n + 4) = 120 * 0 := by linear_combination (norm := parley_norm) (n ^ 4 + 10 * n ^ 3 + 35 * n ^ 2 + 50 * n + 24) * hC8
        -- 2.7.6.10. def:divides d := 120, n := n·(n + 1)·(n + 2)·(n + 3)·(n + 4), from 2.7.6.9
        exact ((Parley.Items.Stdlib.Divisibility.def_divides (d := (120 : ℤ)) (n := n * (n + 1) * (n + 2) * (n + 3) * (n + 4)))).mpr ⟨(0 : ℤ), s2_7_6_9⟩
    · skip
      -- 2.7.7. mun:integer-step m := n + 4, n := 0, from C9
      have s2_7_7 : n + 4 + 1 ≤ 0 := by exact (Parley.Items.Stdlib.Numbers.mun_integer_step (m := n + 4) (n := (0 : ℤ)) hC9)
      -- 2.7.8. inequalities
      have s2_7_8 : 1 ≤ -n - 4 := by linarith only [s2_7_7]
      -- 2.7.9. inequalities, from 2.7.8
      have s2_7_9 : 0 < -n - 4 := by linarith only [s2_7_8]
      have hD1_kind : 0 < -n - 4 := by exact (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := -n - 4) s2_7_9)
      set k : ℤ := -n - 4 with hD1
      have hD1_pos := hD1_kind
      -- 2.7.10. mun:nat-minus-one n := k
      have s2_7_10 : 0 ≤ k - 1 := by exact (Parley.Items.Stdlib.Numbers.mun_nat_minus_one (n := k) hD1_pos)
      set P : ℤ := (k - 1 + 1) * (k - 1 + 2) * (k - 1 + 3) * (k - 1 + 4) * (k - 1 + 5) with hD2
      -- 2.7.11. thm:five-consecutive-natural m := k − 1, from D2, 2.7.10
      have s2_7_11 : (120 : ℤ) ∣ P := by
        try simp only [hD2] at ⊢
        try push_cast at ⊢
        exact (Parley.Proofs.Hammack.FiveConsecutiveDivisible.FiveConsecutiveNatural.five_consecutive_natural (m := k - 1) s2_7_10)
      -- 2.7.12. mun:divides-multiple e := 120, a := P, x := −1, from 2.7.11
      have s2_7_12 : (120 : ℤ) ∣ P * -1 := by exact (Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := (120 : ℤ)) (a := P) (x := (-1 : ℤ)) s2_7_11)
      -- 2.7.13. algebra, from D1, D2
      have s2_7_13 : P * -1 = n * (n + 1) * (n + 2) * (n + 3) * (n + 4) := by
        try simp only [hD1, hD2] at ⊢
        try push_cast at ⊢
        parley_ring
      -- 2.7.14. substitute P·(−1) = n·(n + 1)·(n + 2)·(n + 3)·(n + 4) (line 2.7.13) into line 2.7.12
      (have h := Eq.subst (motive := (fun t : ℤ => (120 : ℤ) ∣ t)) s2_7_13 s2_7_12; push_cast at h ⊢; all_goals exact_mod_cast h)

end Parley.Proofs.Hammack.FiveConsecutiveDivisible.FiveConsecutiveDivisible
