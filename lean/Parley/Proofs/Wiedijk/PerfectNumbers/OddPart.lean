module

public import AlgebraTactics
public import ArithTactics
public import Functions
public import NormTactics
public import OrderTactics
public import Tactics
public import Mathlib.Algebra.Group.Even
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Proofs.Wiedijk.PerfectNumbers
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Sums

/-! Written from proofs/wiedijk/perfect-numbers.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.PerfectNumbers.OddPart

theorem odd_part (n : ℤ) (hH1 : 0 < n) :
    (∃ k : ℤ, 0 ≤ k ∧ (∃ m : ℤ, 0 < m ∧ (Odd m ∧ n = 2 ^ k.toNat * m))) := by
  -- 1. induction on N starting at 0
  have s1 : ∀ N : ℤ, 0 ≤ N → (∀ j : ℤ, j ∈ Finset.Icc 1 N → (∃ k : ℤ, 0 ≤ k ∧ (∃ m : ℤ, 0 < m ∧ (Odd m ∧ j = 2 ^ k.toNat * m)))) := by
    intro N h_N
    replace h_N : 0 ≤ N := by omega
    induction N, h_N using LeanBridges.Functions.le_induction with
    | base =>
      intro j hK1
      try push_cast at hK1
      try have hK1_bounds := Finset.mem_Icc.mp hK1
      -- 1.1. mun:range-bounds a := 1, b := 0, k := j, from K1
      have s1_1 : 1 ≤ j := by exact (Parley.Items.Stdlib.Sums.mun_range_bounds_1 (a := (1 : ℤ)) (b := (0 : ℤ)) (k := j) hK1)
      -- 1.2. mun:range-bounds a := 1, b := 0, k := j, from K1
      have s1_2 : j ≤ 0 := by exact (Parley.Items.Stdlib.Sums.mun_range_bounds_2 (a := (1 : ℤ)) (b := (0 : ℤ)) (k := j) hK1)
      -- 1.3. inequalities, from 1.1
      have s1_3 : ¬ j ≤ 0 := by parley_side
      exact absurd s1_2 s1_3
    | succ N hK2 hIH =>
      intro j hK3
      try push_cast at hK3
      try have hK3_bounds := Finset.mem_Icc.mp hK3
      -- 1.4. mun:range-bounds a := 1, b := N + 1, k := j, from K3
      have s1_4 : 1 ≤ j := by exact (Parley.Items.Stdlib.Sums.mun_range_bounds_1 (a := (1 : ℤ)) (b := N + 1) (k := j) hK3)
      -- 1.5. mun:range-bounds a := 1, b := N + 1, k := j, from K3
      have s1_5 : j ≤ N + 1 := by exact (Parley.Items.Stdlib.Sums.mun_range_bounds_2 (a := (1 : ℤ)) (b := N + 1) (k := j) hK3)
      -- 1.6. mun:even-or-odd n := j
      have s1_6 : Even j ∨ Odd j := by exact (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := j))
      -- 1.7. cases, from 1.6
      have s1_7 : ∃ k : ℤ, 0 ≤ k ∧ (∃ m : ℤ, 0 < m ∧ (Odd m ∧ j = 2 ^ k.toNat * m)) := by
        rcases s1_6 with hC1 | hC2
        · skip
          -- 1.7.1. obtain i: def:even n := j, from C1
          obtain ⟨i, s1_7_1⟩ := ((Parley.Items.Stdlib.Divisibility.def_even (n := j))).mp hC1
          -- 1.7.2. substitute j = 2i (line 1.7.1) into line 1.4
          have s1_7_2 : 1 ≤ 2 * i := by (have h := Eq.subst (motive := (fun t : ℤ => 1 ≤ t)) s1_7_1 s1_4; push_cast at h ⊢; all_goals exact_mod_cast h)
          -- 1.7.3. mun:factor-positive a := 2, b := i
          have r197_1 : (2 : ℤ) ≥ 0 := by parley_arith
          have r197_2 : 2 * i > 0 := by parley_order
          have s1_7_3 : 0 < i := by exact (Parley.Items.Stdlib.Numbers.mun_factor_positive (a := (2 : ℤ)) (b := i) r197_1 (by parley_side))
          -- 1.7.4. mun:pos-int-nat m := i, from 1.7.3
          have s1_7_4 : 0 < i := by exact (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := i) s1_7_3)
          -- 1.7.5. inequalities
          have s1_7_5 : i < 2 * i := by parley_order
          -- 1.7.6. transitivity, from 1.7.5, 1.7.1, 1.5
          have s1_7_6 : i < N + 1 := by parley_order
          -- 1.7.7. mun:integer-step m := i, n := N + 1, from 1.7.6
          have s1_7_7 : i + 1 ≤ N + 1 := by exact (Parley.Items.Stdlib.Numbers.mun_integer_step (m := i) (n := N + 1) s1_7_6)
          -- 1.7.8. inequalities
          have s1_7_8 : i ≤ N := by parley_order
          -- 1.7.9. def:range-between k := i, a := 1, b := N, from 1.7.8
          have r222_1 : 1 ≤ i := by parley_order
          have s1_7_9 : i ∈ Finset.Icc (1 : ℤ) N := ((Parley.Items.Stdlib.Sums.def_range_between (k := i) (a := (1 : ℤ)) (b := N))).mpr ⟨r222_1, s1_7_8⟩
          -- 1.7.10. instantiate j := i in IH, from 1.7.9
          have s1_7_10 : ∃ k : ℤ, 0 ≤ k ∧ (∃ m : ℤ, 0 < m ∧ (Odd m ∧ i = 2 ^ k.toNat * m)) := by exact (hIH i s1_7_9)
          -- 1.7.11. D1, from 1.7.10
          have s1_7_11 : ∃ k : ℤ, 0 ≤ k ∧ (∃ m : ℤ, 0 < m ∧ (Odd m ∧ i = 2 ^ k.toNat * m)) := by parley_side
          -- 1.7.12. obtain k, m from line 1.7.11
          obtain ⟨k, s1_7_12a, m, s1_7_12b, ⟨s1_7_12c, s1_7_12d⟩⟩ := s1_7_11
          -- 1.7.13. mun:exponent-step a := 2, m := k
          have s1_7_13 : (2 ^ (k + 1).toNat : ℤ) = 2 ^ k.toNat * 2 := by exact (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k) s1_7_12a)
          -- 1.7.14. algebra, from 1.7.1, 1.7.12, 1.7.13
          have s1_7_14 : j = 2 ^ (k + 1).toNat * m := by linear_combination (norm := parley_norm) s1_7_1 + (2) * s1_7_12d + (-m) * s1_7_13
          -- 1.7.15. exhibit, from 1.7.12, 1.7.14
          exact ⟨k + 1, by parley_side, m, s1_7_12b, ⟨s1_7_12c, s1_7_14⟩⟩
        · skip
          -- 1.7.16. algebra
          have s1_7_16 : j = 2 ^ 0 * j := by parley_ring
          -- 1.7.17. exhibit, from C2, 1.7.16
          exact ⟨(0 : ℤ), by parley_side, j, by parley_side, ⟨hC2, by simpa only [Int.reduceToNat] using s1_7_16⟩⟩
      -- 1.8. D1, from 1.7
      parley_side
  -- 2. instantiate N := n in line 1
  have s2 : ∀ j : ℤ, j ∈ Finset.Icc 1 n → (∃ k : ℤ, 0 ≤ k ∧ (∃ m : ℤ, 0 < m ∧ (Odd m ∧ j = 2 ^ k.toNat * m))) := by intro j h_j; exact (s1 n (le_of_lt hH1) j (by parley_side))
  -- 3. def:range-between k := n, a := 1, b := n
  have r260_1 : 1 ≤ n := by parley_order
  have r260_2 : n ≤ n := by parley_order
  have s3 : n ∈ Finset.Icc (1 : ℤ) n := ((Parley.Items.Stdlib.Sums.def_range_between (k := n) (a := (1 : ℤ)) (b := n))).mpr ⟨r260_1, r260_2⟩
  -- 4. instantiate j := n in line 2, from 3
  have s4 : ∃ k : ℤ, 0 ≤ k ∧ (∃ m : ℤ, 0 < m ∧ (Odd m ∧ n = 2 ^ k.toNat * m)) := by exact (s2 n s3)
  -- 5. D1, from 4
  parley_side

end Parley.Proofs.Wiedijk.PerfectNumbers.OddPart
