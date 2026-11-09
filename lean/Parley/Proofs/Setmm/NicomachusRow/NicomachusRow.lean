module

public import AlgebraTactics
public import NormTactics
public import PowerTactics
public import SubstTactics
public import Tactics
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Data.Finset.Defs
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
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Sums
public import Parley.Proofs.Setmm.OddNumbersSum.OddNumbersSum

/-! Written from proofs/setmm/nicomachus-row.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.NicomachusRow.NicomachusRow

set_option maxHeartbeats 400000 in
theorem nicomachus_row (N : ℤ) (hH1 : 0 ≤ N) :
    (∑ k ∈ Finset.Icc (1 : ℤ) N, (N ^ 2 - N + (2 * k - 1) : ℤ)) = N ^ 3 := by
  -- 1. def:nat0 n := N
  have s1 : 0 < N ∨ N = 0 := by simpa only [Int.cast_id, exists_eq_right] using ((Parley.Items.Stdlib.Numbers.def_nat0 (n := N))).mp (by parley_side)
  -- 2. cases, from 1
  rcases s1 with hC1 | hC2
  · skip
    -- 2.1. mun:sum-add a := 1, b := N
    have s2_1 : (∑ k ∈ Finset.Icc (1 : ℤ) N, (N ^ 2 - N + (2 * k - 1) : ℤ)) = (∑ k ∈ Finset.Icc (1 : ℤ) N, (N ^ 2 - N : ℤ)) + (∑ k ∈ Finset.Icc (1 : ℤ) N, (2 * k - 1 : ℤ)) := by exact (Parley.Items.Stdlib.Sums.mun_sum_add (t := (fun k : ℤ => N ^ 2 - N)) (u := (fun k : ℤ => 2 * k - 1)) (a := (1 : ℤ)) (b := N))
    -- 2.2. substitute
    have r26_1 : 1 ≤ N := by parley_side
    have s2_2 : (∑ k ∈ Finset.Icc (1 : ℤ) N, (N ^ 2 - N + (2 * k - 1) : ℤ)) = (N - 1 + 1) * (N ^ 2 - N) + (∑ k ∈ Finset.Icc (1 : ℤ) N, (2 * k - 1 : ℤ)) := by
      have c1 : (∑ k ∈ Finset.Icc (1 : ℤ) N, (N ^ 2 - N : ℤ)) = (N - 1 + 1) * (N ^ 2 - N) := by exact (Parley.Items.Stdlib.Sums.mun_sum_constant (a := (1 : ℤ)) (b := N) r26_1 (c := N ^ 2 - N))
      have row1 : (∑ k ∈ Finset.Icc (1 : ℤ) N, (N ^ 2 - N + (2 * k - 1) : ℤ)) = (N - 1 + 1) * (N ^ 2 - N) + (∑ k ∈ Finset.Icc (1 : ℤ) N, (2 * k - 1 : ℤ)) := by parley_subst_at c1 s2_1
      exact row1
    -- 2.3. substitute
    have s2_3 : (∑ k ∈ Finset.Icc (1 : ℤ) N, (N ^ 2 - N + (2 * k - 1) : ℤ)) = (N - 1 + 1) * (N ^ 2 - N) + N ^ 2 := by
      have c1 : (∑ k ∈ Finset.Icc (1 : ℤ) N, (2 * k - 1 : ℤ)) = N ^ 2 := by exact (Parley.Proofs.Setmm.OddNumbersSum.OddNumbersSum.odd_numbers_sum (N := N) (by parley_side))
      have row1 : (∑ k ∈ Finset.Icc (1 : ℤ) N, (N ^ 2 - N + (2 * k - 1) : ℤ)) = (N - 1 + 1) * (N ^ 2 - N) + N ^ 2 := by parley_subst_at c1 s2_2
      exact row1
    -- 2.4. calculation
    calc (∑ k ∈ Finset.Icc (1 : ℤ) N, (N ^ 2 - N + (2 * k - 1) : ℤ)) = (N - 1 + 1) * (N ^ 2 - N) + N ^ 2 := by parley_side
      _ = N ^ 3 := by parley_ring
  · skip
    -- 2.5. mun:sum-single a := 0
    have s2_5 : (∑ k ∈ Finset.Icc (0 : ℤ) (0 : ℤ), (0 ^ 2 - 0 + (2 * k - 1) : ℤ)) = 0 ^ 2 - 0 + (2 * 0 - 1) := by exact (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun k : ℤ => 0 ^ 2 - 0 + (2 * k - 1))) (a := (0 : ℤ)))
    -- 2.6. mun:sum-first n := 0
    have s2_6 : (∑ k ∈ Finset.Icc (0 : ℤ) (0 : ℤ), (0 ^ 2 - 0 + (2 * k - 1) : ℤ)) = 0 ^ 2 - 0 + (2 * 0 - 1) + (∑ k ∈ Finset.Icc (1 : ℤ) (0 : ℤ), (0 ^ 2 - 0 + (2 * k - 1) : ℤ)) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_sum_first (t := (fun k : ℤ => 0 ^ 2 - 0 + (2 * k - 1))) (n := (0 : ℤ)) (by parley_side)) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_first (t := (fun k : ℤ => 0 ^ 2 - 0 + (2 * k - 1))) (n := (0 : ℤ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_first (t := (fun k : ℤ => 0 ^ 2 - 0 + (2 * k - 1))) (n := (0 : ℤ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_sum_first (t := (fun k : ℤ => 0 ^ 2 - 0 + (2 * k - 1))) (n := (0 : ℤ)) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Sums.mun_sum_first (t := (fun k : ℤ => 0 ^ 2 - 0 + (2 * k - 1))) (n := (0 : ℤ)) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Sums.mun_sum_first (t := (fun k : ℤ => 0 ^ 2 - 0 + (2 * k - 1))) (n := (0 : ℤ)) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_first (t := (fun k : ℤ => 0 ^ 2 - 0 + (2 * k - 1))) (n := (0 : ℤ)) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_first (t := (fun k : ℤ => 0 ^ 2 - 0 + (2 * k - 1))) (n := (0 : ℤ)) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_first (t := (fun k : ℤ => 0 ^ 2 - 0 + (2 * k - 1))) (n := (0 : ℤ)) (by parley_side)); parley_side)
    -- 2.7. algebra, from 2.5, 2.6
    have s2_7 : (∑ k ∈ Finset.Icc (1 : ℤ) (0 : ℤ), (0 ^ 2 - 0 + (2 * k - 1) : ℤ)) = 0 := by linear_combination (norm := parley_norm) s2_5 + (-1) * s2_6
    -- 2.8. calculation
    have s2_8 : (∑ k ∈ Finset.Icc (1 : ℤ) (0 : ℤ), (0 ^ 2 - 0 + (2 * k - 1) : ℤ)) = 0 ^ 3 := by
      calc (∑ k ∈ Finset.Icc (1 : ℤ) (0 : ℤ), (0 ^ 2 - 0 + (2 * k - 1) : ℤ)) = 0 := by parley_side
        _ = 0 ^ 3 := by norm_num
    -- 2.9. substitute N = 0 (C2) into line 2.8
    parley_subst_at hC2 s2_8

end Parley.Proofs.Setmm.NicomachusRow.NicomachusRow
