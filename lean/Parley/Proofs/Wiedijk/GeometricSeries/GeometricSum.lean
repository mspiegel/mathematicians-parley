module

public import AlgebraTactics
public import PowerTactics
public import SubstTactics
public import Tactics
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Sums

/-! Written from proofs/wiedijk/geometric-series.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.GeometricSeries.GeometricSum

theorem geometric_sum (a : ℝ) (hH2 : a ≠ 1) (n : ℕ) :
    (∑ j ∈ Finset.Icc (0 : ℤ) (n : ℤ), (a ^ j : ℝ)) = (1 - a ^ (n + 1)) / (1 - a) := by
  -- 1. induction on k starting at 0
  have s1 : ∀ k : ℕ, (∑ j ∈ Finset.Icc (0 : ℤ) (k : ℤ), (a ^ j : ℝ)) = (1 - a ^ (k + 1)) / (1 - a) := by
    intro k
    induction k with
    | zero =>
      -- 1.1. calculation
      have s1_1 : (∑ j ∈ Finset.Icc (0 : ℤ) (0 : ℤ), (a ^ j : ℝ)) = 1 := by
        calc (∑ j ∈ Finset.Icc (0 : ℤ) (0 : ℤ), (a ^ j : ℝ)) = (∑ j ∈ Finset.Icc (0 : ℤ) (0 : ℤ), (a ^ j : ℝ)) := by parley_side
          _ = a ^ 0 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => a ^ j)) (a := (0 : ℤ))) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => a ^ j)) (a := (0 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => a ^ j)) (a := (0 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => a ^ j)) (a := (0 : ℤ))) | exact_mod_cast ((Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => a ^ j)) (a := (0 : ℤ)))).symm | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => a ^ j)) (a := (0 : ℤ))); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => a ^ j)) (a := (0 : ℤ))); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => a ^ j)) (a := (0 : ℤ))); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => a ^ j)) (a := (0 : ℤ))); parley_side)
          _ = 1 := by parley_ring
      -- 1.2. calculation
      have r26_1 : 1 - a ≠ 0 := by intro h; exact hH2 (by linear_combination (norm := parley_norm) (-1) * h)
      have s1_2 : (∑ j ∈ Finset.Icc (0 : ℤ) (0 : ℤ), (a ^ j : ℝ)) = (1 - a) / (1 - a) := by
        calc (∑ j ∈ Finset.Icc (0 : ℤ) (0 : ℤ), (a ^ j : ℝ)) = 1 := by parley_side
          _ = (1 - a) / (1 - a) := by parley_ring
      all_goals parley_side
    | succ k hIH =>
      -- 1.3. calculation
      have s1_3 : (∑ j ∈ Finset.Icc (0 : ℤ) ((k : ℤ) + 1), (a ^ j : ℝ)) = (∑ j ∈ Finset.Icc (0 : ℤ) (k : ℤ), (a ^ j : ℝ)) + a ^ (k + 1) := by
        calc (∑ j ∈ Finset.Icc (0 : ℤ) ((k : ℤ) + 1), (a ^ j : ℝ)) = (∑ j ∈ Finset.Icc (0 : ℤ) ((k : ℤ) + 1), (a ^ j : ℝ)) := by parley_side
          _ = (∑ j ∈ Finset.Icc (0 : ℤ) (k : ℤ), (a ^ j : ℝ)) + a ^ (k + 1) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_sum_last (t := (fun j : ℤ => a ^ j)) (n := k)) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_last (t := (fun j : ℤ => a ^ j)) (n := k)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_last (t := (fun j : ℤ => a ^ j)) (n := k)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_sum_last (t := (fun j : ℤ => a ^ j)) (n := k)) | exact_mod_cast ((Parley.Items.Stdlib.Sums.mun_sum_last (t := (fun j : ℤ => a ^ j)) (n := k))).symm | (have h := (Parley.Items.Stdlib.Sums.mun_sum_last (t := (fun j : ℤ => a ^ j)) (n := k)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_last (t := (fun j : ℤ => a ^ j)) (n := k)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_last (t := (fun j : ℤ => a ^ j)) (n := k)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_last (t := (fun j : ℤ => a ^ j)) (n := k)); parley_side)
          _ = (∑ j ∈ Finset.Icc (0 : ℤ) (k : ℤ), (a ^ j : ℝ)) + a ^ (k + 1) := by parley_side
      -- 1.4. mun:exponent-step m := k + 1
      have s1_4 : a ^ (k + 1 + 1) = a ^ (k + 1) * a := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := a) (m := k + 1)) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := a) (m := k + 1)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := a) (m := k + 1)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := a) (m := k + 1)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_exponent_step (a := a) (m := k + 1))).symm | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := a) (m := k + 1)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := a) (m := k + 1)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := a) (m := k + 1)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := a) (m := k + 1)); parley_side)
      -- 1.5. calculation
      have r45_1 : 1 - a ≠ 0 := by intro h; exact hH2 (by linear_combination (norm := parley_norm) (-1) * h)
      have s1_5 : (∑ j ∈ Finset.Icc (0 : ℤ) ((k : ℤ) + 1), (a ^ j : ℝ)) = (1 - a ^ (k + 1 + 1)) / (1 - a) := by
        calc (∑ j ∈ Finset.Icc (0 : ℤ) ((k : ℤ) + 1), (a ^ j : ℝ)) = (∑ j ∈ Finset.Icc (0 : ℤ) (k : ℤ), (a ^ j : ℝ)) + a ^ (k + 1) := by parley_side
          _ = (1 - a ^ (k + 1)) / (1 - a) + a ^ (k + 1) := by parley_subst hIH
          _ = (1 - a ^ (k + 1) * a) / (1 - a) := by parley_ring
          _ = (1 - a ^ (k + 1 + 1)) / (1 - a) := by parley_subst s1_4
      all_goals parley_side
  -- 2. instantiate k := n in line 1
  have s2 : (∑ j ∈ Finset.Icc (0 : ℤ) (n : ℤ), (a ^ j : ℝ)) = (1 - a ^ (n + 1)) / (1 - a) := by first | linear_combination (norm := parley_norm) (s1 n) | (have h := (s1 n); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (s1 n); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (s1 n) | exact_mod_cast ((s1 n)).symm | (have h := (s1 n); rify; linear_combination (norm := parley_norm) h) | (have h := (s1 n); qify; linear_combination (norm := parley_norm) h) | (have h := (s1 n); parley_int_power h) | (have h := (s1 n); parley_side)
  all_goals exact s2

end Parley.Proofs.Wiedijk.GeometricSeries.GeometricSum
