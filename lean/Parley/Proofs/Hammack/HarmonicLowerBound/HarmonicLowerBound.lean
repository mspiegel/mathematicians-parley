module

public import ArithTactics
public import Functions
public import NormTactics
public import OrderTactics
public import PowerTactics
public import SubstTactics
public import Tactics
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Rat.Defs
public import Mathlib.Data.Rat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.BigOperators
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Parley.Items.Stdlib.Sums
public import Parley.Proofs.Hammack.HarmonicLowerBound.HarmonicDoubling

/-! Written from proofs/hammack/harmonic-lower-bound.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.HarmonicLowerBound.HarmonicLowerBound

theorem harmonic_lower_bound (n : ℤ) (hH1 : 0 < n) :
    (∑ k ∈ Finset.Icc (1 : ℤ) (2 ^ n.toNat : ℤ), (1 / (k : ℚ) : ℚ)) ≥ 1 + (n : ℚ) / 2 := by
  -- 1. proof
  -- what this block shows, Lean's types give
  -- 2. induction on m starting at 1
  have s2 : ∀ m : ℤ, 0 < m → (∑ j ∈ Finset.Icc (1 : ℤ) (2 ^ m.toNat : ℤ), (1 / (j : ℚ) : ℚ)) ≥ 1 + (m : ℚ) / 2 := by
    intro m h_m
    replace h_m : 1 ≤ m := by omega
    induction m, h_m using LeanBridges.Functions.le_induction with
    | base =>
      -- 2.1. mun:sum-single a := 1, from 1
      have s2_1 : (∑ j ∈ Finset.Icc (1 : ℤ) (1 : ℤ), (1 / (j : ℚ) : ℚ)) = 1 / 1 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => 1 / (j : ℚ))) (a := (1 : ℤ))) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => 1 / (j : ℚ))) (a := (1 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => 1 / (j : ℚ))) (a := (1 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => 1 / (j : ℚ))) (a := (1 : ℤ))) | exact_mod_cast ((Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => 1 / (j : ℚ))) (a := (1 : ℤ)))).symm | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => 1 / (j : ℚ))) (a := (1 : ℤ))); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => 1 / (j : ℚ))) (a := (1 : ℤ))); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => 1 / (j : ℚ))) (a := (1 : ℤ))); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => 1 / (j : ℚ))) (a := (1 : ℤ))); parley_side)
      -- 2.2. calculation
      have r135_1 : (1 : ℤ) ≥ 1 := by parley_arith
      have s2_2 : (∑ j ∈ Finset.Icc (1 : ℤ) (2 ^ 1 : ℤ), (1 / (j : ℚ) : ℚ)) ≥ 1 + 1 / 2 := by
        calc (∑ j ∈ Finset.Icc (1 : ℤ) (2 ^ 1 : ℤ), (1 / (j : ℚ) : ℚ)) = (∑ j ∈ Finset.Icc (1 : ℤ) (1 + 1 : ℤ), (1 / (j : ℚ) : ℚ)) := by norm_num
          _ = (∑ j ∈ Finset.Icc (1 : ℤ) (1 : ℤ), (1 / (j : ℚ) : ℚ)) + 1 / (1 + 1) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => 1 / (j : ℚ))) (a := (1 : ℤ)) (n := (1 : ℤ)) r135_1) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => 1 / (j : ℚ))) (a := (1 : ℤ)) (n := (1 : ℤ)) r135_1); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => 1 / (j : ℚ))) (a := (1 : ℤ)) (n := (1 : ℤ)) r135_1); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => 1 / (j : ℚ))) (a := (1 : ℤ)) (n := (1 : ℤ)) r135_1) | exact_mod_cast ((Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => 1 / (j : ℚ))) (a := (1 : ℤ)) (n := (1 : ℤ)) r135_1)).symm | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => 1 / (j : ℚ))) (a := (1 : ℤ)) (n := (1 : ℤ)) r135_1); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => 1 / (j : ℚ))) (a := (1 : ℤ)) (n := (1 : ℤ)) r135_1); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => 1 / (j : ℚ))) (a := (1 : ℤ)) (n := (1 : ℤ)) r135_1); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => 1 / (j : ℚ))) (a := (1 : ℤ)) (n := (1 : ℤ)) r135_1); parley_side)
          _ = 1 / 1 + 1 / (1 + 1) := by parley_subst s2_1
          _ ≥ 1 + 1 / 2 := by norm_num
      simpa only [Int.reduceToNat, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Int.cast_ofNat, Int.cast_zero, Int.cast_one] using s2_2
    | succ m hK hIH =>
      -- 2.3. thm:harmonic-doubling j := m
      have s2_3 : (∑ j ∈ Finset.Icc (1 : ℤ) (2 ^ (m + 1).toNat : ℤ), (1 / (j : ℚ) : ℚ)) ≥ (∑ j ∈ Finset.Icc (1 : ℤ) (2 ^ m.toNat : ℤ), (1 / (j : ℚ) : ℚ)) + 1 / 2 := (Parley.Proofs.Hammack.HarmonicLowerBound.HarmonicDoubling.harmonic_doubling (j := m) (by parley_side))
      -- 2.4. inequalities
      have s2_4 : (∑ j ∈ Finset.Icc (1 : ℤ) (2 ^ m.toNat : ℤ), (1 / (j : ℚ) : ℚ)) + 1 / 2 ≥ 1 + ((m : ℚ) + 1) / 2 := by parley_order
      -- 2.5. transitivity, from 2.3, 2.4
      have s2_5 : (∑ j ∈ Finset.Icc (1 : ℤ) (2 ^ (m + 1).toNat : ℤ), (1 / (j : ℚ) : ℚ)) ≥ 1 + ((m : ℚ) + 1) / 2 := by parley_order
      first | exact_mod_cast s2_5 | (have h := s2_5; push_cast at h ⊢; exact h) | simpa using s2_5
  -- 3. instantiate m := n in line 2
  first | (have h := (s2 n (by parley_side)); simp (disch := first | omega | positivity | nlinarith) only [parley_zpow_toNat] at h ⊢; first | exact_mod_cast h | linarith) | linarith [(s2 n (by parley_side))] | (have h := (s2 n (by parley_side)); push_cast at h; linarith) | exact_mod_cast (s2 n (by parley_side)) | (have h := (s2 n (by parley_side)); parley_side)

end Parley.Proofs.Hammack.HarmonicLowerBound.HarmonicLowerBound
