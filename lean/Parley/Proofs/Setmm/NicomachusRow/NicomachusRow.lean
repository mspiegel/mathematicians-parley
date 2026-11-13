module

public import AlgebraTactics
public import InstanceTactics
public import NormTactics
public import Tactics
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.BigOperators
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Positivity.Finset
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Sums
public import Parley.Proofs.Setmm.OddNumbersSum.OddNumbersSum

/-! Written from proofs/setmm/nicomachus-row.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.NicomachusRow.NicomachusRow

theorem nicomachus_row (N : ℤ) (hH1 : 0 ≤ N) :
    (∑ k ∈ Finset.Icc (1 : ℤ) N, (N ^ 2 - N + (2 * k - 1) : ℤ)) = N ^ 3 := by
  -- 1. def:nat0 n := N
  have s1 : 0 < N ∨ N = 0 := by
    have hI : 0 < N ∨ N = 0 := by parley_instance (((Parley.Items.Stdlib.Numbers.def_nat0 (n := N))).mp ⟨N, hH1, rfl⟩)
    exact hI
  -- 2. cases, from 1
  rcases s1 with hC1 | hC2
  · skip
    -- 2.1. mun:sum-add a := 1, b := N
    have s2_1 : (∑ k ∈ Finset.Icc (1 : ℤ) N, (N ^ 2 - N + (2 * k - 1) : ℤ)) = (∑ k ∈ Finset.Icc (1 : ℤ) N, (N ^ 2 - N : ℤ)) + (∑ k ∈ Finset.Icc (1 : ℤ) N, (2 * k - 1 : ℤ)) := by exact (Parley.Items.Stdlib.Sums.mun_sum_add (t := (fun k : ℤ => N ^ 2 - N)) (u := (fun k : ℤ => 2 * k - 1)) (a := (1 : ℤ)) (b := N))
    -- 2.2. substitute
    have r26_1 : 1 ≤ N := by exact hC1
    have s2_2 : (∑ k ∈ Finset.Icc (1 : ℤ) N, (N ^ 2 - N + (2 * k - 1) : ℤ)) = (N - 1 + 1) * (N ^ 2 - N) + (∑ k ∈ Finset.Icc (1 : ℤ) N, (2 * k - 1 : ℤ)) := by
      have c1 : (∑ k ∈ Finset.Icc (1 : ℤ) N, (N ^ 2 - N : ℤ)) = (N - 1 + 1) * (N ^ 2 - N) := by exact (Parley.Items.Stdlib.Sums.mun_sum_constant (a := (1 : ℤ)) (b := N) r26_1 (c := N ^ 2 - N))
      have row1 : (∑ k ∈ Finset.Icc (1 : ℤ) N, (N ^ 2 - N + (2 * k - 1) : ℤ)) = (N - 1 + 1) * (N ^ 2 - N) + (∑ k ∈ Finset.Icc (1 : ℤ) N, (2 * k - 1 : ℤ)) := by (have h := Eq.subst (motive := (fun t : ℤ => (∑ k ∈ Finset.Icc (1 : ℤ) N, (N ^ 2 - N + (2 * k - 1) : ℤ)) = t + (∑ k ∈ Finset.Icc (1 : ℤ) N, (2 * k - 1 : ℤ)))) c1 s2_1; push_cast at h ⊢; all_goals exact_mod_cast h)
      exact row1
    -- 2.3. substitute
    have s2_3 : (∑ k ∈ Finset.Icc (1 : ℤ) N, (N ^ 2 - N + (2 * k - 1) : ℤ)) = (N - 1 + 1) * (N ^ 2 - N) + N ^ 2 := by
      have c1 : (∑ k ∈ Finset.Icc (1 : ℤ) N, (2 * k - 1 : ℤ)) = N ^ 2 := by exact (Parley.Proofs.Setmm.OddNumbersSum.OddNumbersSum.odd_numbers_sum (N := N) hH1)
      have row1 : (∑ k ∈ Finset.Icc (1 : ℤ) N, (N ^ 2 - N + (2 * k - 1) : ℤ)) = (N - 1 + 1) * (N ^ 2 - N) + N ^ 2 := by (have h := Eq.subst (motive := (fun t : ℤ => (∑ k ∈ Finset.Icc (1 : ℤ) N, (N ^ 2 - N + (2 * k - 1) : ℤ)) = (N - 1 + 1) * (N ^ 2 - N) + t)) c1 s2_2; push_cast at h ⊢; all_goals exact_mod_cast h)
      exact row1
    -- 2.4. calculation
    calc (∑ k ∈ Finset.Icc (1 : ℤ) N, (N ^ 2 - N + (2 * k - 1) : ℤ)) = (N - 1 + 1) * (N ^ 2 - N) + N ^ 2 := s2_3
      _ = N ^ 3 := by parley_ring
  · skip
    -- 2.5. mun:sum-single a := 0
    have s2_5 : (∑ k ∈ Finset.Icc (0 : ℤ) (0 : ℤ), (0 ^ 2 - 0 + (2 * k - 1) : ℤ)) = 0 ^ 2 - 0 + (2 * 0 - 1) := by exact (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun k : ℤ => 0 ^ 2 - 0 + (2 * k - 1))) (a := (0 : ℤ)))
    -- 2.6. mun:sum-first n := 0
    have s2_6 : (∑ k ∈ Finset.Icc (0 : ℤ) (0 : ℤ), (0 ^ 2 - 0 + (2 * k - 1) : ℤ)) = 0 ^ 2 - 0 + (2 * 0 - 1) + (∑ k ∈ Finset.Icc (1 : ℤ) (0 : ℤ), (0 ^ 2 - 0 + (2 * k - 1) : ℤ)) := by
      have hI : (∑ a ∈ Finset.Icc (0 : ℤ) (0 : ℤ), (0 ^ 2 - 0 + (2 * a - 1) : ℤ)) = 0 ^ 2 - 0 + (2 * 0 - 1) + (∑ a ∈ Finset.Icc (0 + 1 : ℤ) (0 : ℤ), (0 ^ 2 - 0 + (2 * a - 1) : ℤ)) := by parley_instance ((Parley.Items.Stdlib.Sums.mun_sum_first (t := (fun k : ℤ => 0 ^ 2 - 0 + (2 * k - 1))) (n := (0 : ℤ)) (by norm_num)))
      simpa only [Int.cast_one, Int.cast_zero, sub_zero, zero_add] using hI
    -- 2.7. algebra, from 2.5, 2.6
    have s2_7 : (∑ k ∈ Finset.Icc (1 : ℤ) (0 : ℤ), (0 ^ 2 - 0 + (2 * k - 1) : ℤ)) = 0 := by linear_combination (norm := parley_norm) s2_5 + (-1) * s2_6
    -- 2.8. calculation
    have s2_8 : (∑ k ∈ Finset.Icc (1 : ℤ) (0 : ℤ), (0 ^ 2 - 0 + (2 * k - 1) : ℤ)) = 0 ^ 3 := by
      calc (∑ k ∈ Finset.Icc (1 : ℤ) (0 : ℤ), (0 ^ 2 - 0 + (2 * k - 1) : ℤ)) = 0 := s2_7
        _ = 0 ^ 3 := by norm_num
    -- 2.9. substitute N = 0 (C2) into line 2.8
    (have h := Eq.subst (motive := (fun t : ℤ => (∑ k ∈ Finset.Icc (1 : ℤ) t, (t ^ 2 - t + (2 * k - 1) : ℤ)) = t ^ 3)) hC2.symm s2_8; push_cast at h ⊢; all_goals exact_mod_cast h)

end Parley.Proofs.Setmm.NicomachusRow.NicomachusRow
