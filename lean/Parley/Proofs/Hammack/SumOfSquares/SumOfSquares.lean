module

public import AlgebraTactics
public import Functions
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
public import Mathlib.Data.Rat.Defs
public import Mathlib.Data.Rat.Init
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
public import Mathlib.Tactic.Set
public import Parley.Items.Stdlib.Sums

/-! Written from proofs/hammack/sum-of-squares.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.SumOfSquares.SumOfSquares

theorem sum_of_squares (n : ℤ) (hH1 : 0 < n) :
    (∑ k ∈ Finset.Icc (1 : ℤ) n, ((k : ℚ) ^ 2 : ℚ)) = (n : ℚ) * ((n : ℚ) + 1) * (2 * (n : ℚ) + 1) / 6 := by
  set S : ℤ → ℤ := fun m => ∑ j ∈ Finset.Icc (1 : ℤ) m, (j ^ 2 : ℤ) with hD1
  -- 1. induction on k starting at 1
  have s1 : ∀ k : ℤ, 0 < k → (S k : ℚ) = (k : ℚ) * ((k : ℚ) + 1) * (2 * (k : ℚ) + 1) / 6 := by
    intro k h_k
    replace h_k : 1 ≤ k := by omega
    induction k, h_k using LeanBridges.Functions.le_induction with
    | base =>
      -- 1.1. calculation
      have s1_1 : (S 1 : ℚ) = 1 * (1 + 1) * (2 * 1 + 1) / 6 := by
        calc (S 1 : ℚ) = (∑ j ∈ Finset.Icc (1 : ℤ) (1 : ℤ), ((j : ℚ) ^ 2 : ℚ)) := by first | (simp (disch := omega) only [hD1]; done) | (simp (disch := omega) only [hD1]; push_cast; norm_num; done) | parley_side
          _ = 1 ^ 2 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (j : ℚ) ^ 2)) (a := (1 : ℤ))) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (j : ℚ) ^ 2)) (a := (1 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (j : ℚ) ^ 2)) (a := (1 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (j : ℚ) ^ 2)) (a := (1 : ℤ))) | exact_mod_cast ((Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (j : ℚ) ^ 2)) (a := (1 : ℤ)))).symm | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (j : ℚ) ^ 2)) (a := (1 : ℤ))); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (j : ℚ) ^ 2)) (a := (1 : ℤ))); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (j : ℚ) ^ 2)) (a := (1 : ℤ))); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (j : ℚ) ^ 2)) (a := (1 : ℤ))); parley_side)
          _ = 1 * (1 + 1) * (2 * 1 + 1) / 6 := by norm_num
      all_goals parley_side
    | succ k hK hIH =>
      -- 1.2. calculation
      have r27_1 : k ≥ 1 := by parley_side
      have s1_2 : S (k + 1) = S k + (k + 1) ^ 2 := by
        calc S (k + 1) = (∑ j ∈ Finset.Icc (1 : ℤ) (k + 1), (j ^ 2 : ℤ)) := by first | (simp (disch := omega) only [hD1]; done) | (simp (disch := omega) only [hD1]; push_cast; norm_num; done) | parley_side
          _ = (∑ j ∈ Finset.Icc (1 : ℤ) k, (j ^ 2 : ℤ)) + (k + 1) ^ 2 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => j ^ 2)) (a := (1 : ℤ)) (n := k) (by parley_side)) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => j ^ 2)) (a := (1 : ℤ)) (n := k) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => j ^ 2)) (a := (1 : ℤ)) (n := k) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => j ^ 2)) (a := (1 : ℤ)) (n := k) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => j ^ 2)) (a := (1 : ℤ)) (n := k) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => j ^ 2)) (a := (1 : ℤ)) (n := k) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => j ^ 2)) (a := (1 : ℤ)) (n := k) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => j ^ 2)) (a := (1 : ℤ)) (n := k) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => j ^ 2)) (a := (1 : ℤ)) (n := k) (by parley_side)); parley_side)
          _ = S k + (k + 1) ^ 2 := by first | (simp (disch := omega) only [hD1]; done) | (simp (disch := omega) only [hD1]; push_cast; norm_num; done) | parley_side
      -- 1.3. calculation
      have s1_3 : (S (k + 1) : ℚ) = ((k : ℚ) + 1) * ((k : ℚ) + 1 + 1) * (2 * ((k : ℚ) + 1) + 1) / 6 := by
        calc (S (k + 1) : ℚ) = (S k : ℚ) + ((k : ℚ) + 1) ^ 2 := by parley_side
          _ = (k : ℚ) * ((k : ℚ) + 1) * (2 * (k : ℚ) + 1) / 6 + ((k : ℚ) + 1) ^ 2 := by parley_subst hIH
          _ = ((k : ℚ) + 1) * ((k : ℚ) + 1 + 1) * (2 * ((k : ℚ) + 1) + 1) / 6 := by parley_ring
      all_goals parley_side
  -- 2. calculation
  have s2 : (∑ k ∈ Finset.Icc (1 : ℤ) n, ((k : ℚ) ^ 2 : ℚ)) = (n : ℚ) * ((n : ℚ) + 1) * (2 * (n : ℚ) + 1) / 6 := by
    calc (∑ k ∈ Finset.Icc (1 : ℤ) n, ((k : ℚ) ^ 2 : ℚ)) = (S n : ℚ) := by first | (simp (disch := omega) only [hD1]; done) | (simp (disch := omega) only [hD1]; push_cast; norm_num; done) | parley_side
      _ = (n : ℚ) * ((n : ℚ) + 1) * (2 * (n : ℚ) + 1) / 6 := by first | linear_combination (norm := parley_norm) (s1 n (by parley_side)) | (have h := (s1 n (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (s1 n (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (s1 n (by parley_side)) | exact_mod_cast ((s1 n (by parley_side))).symm | (have h := (s1 n (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (s1 n (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (s1 n (by parley_side)); parley_int_power h) | (have h := (s1 n (by parley_side)); parley_side)
  all_goals exact s2

end Parley.Proofs.Hammack.SumOfSquares.SumOfSquares
