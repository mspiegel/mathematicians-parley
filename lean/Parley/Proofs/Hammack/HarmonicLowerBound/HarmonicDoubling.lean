module

public import AlgebraTactics
public import InstanceTactics
public import NormTactics
public import Tactics
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Rat.Defs
public import Mathlib.Data.Rat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.PartialOrder
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
public import Mathlib.Tactic.Positivity.Finset
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Sums

/-! Written from proofs/hammack/harmonic-lower-bound.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.HarmonicLowerBound.HarmonicDoubling

theorem harmonic_doubling (j : ℤ) (hH1 : 0 ≤ j) :
    (∑ k ∈ Finset.Icc (1 : ℤ) (2 ^ (j + 1).toNat : ℤ), (1 / (k : ℚ) : ℚ)) ≥ (∑ k ∈ Finset.Icc (1 : ℤ) (2 ^ j.toNat : ℤ), (1 / (k : ℚ) : ℚ)) + 1 / 2 := by
  -- 1. mun:exponent-step a := 2, m := j
  have s1 : (2 ^ (j + 1).toNat : ℤ) = 2 ^ j.toNat * 2 := by exact (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := j) hH1)
  -- 2. mun:power-nat a := 2, m := j
  have s2 : (0 : ℤ) < 2 ^ j.toNat := by exact (Parley.Items.Stdlib.Numbers.mun_power_nat (a := (2 : ℤ)) (by norm_num) (m := j) hH1)
  -- 3. mun:power-nat a := 2, m := j + 1
  have s3 : (0 : ℤ) < 2 ^ (j + 1).toNat := by exact (Parley.Items.Stdlib.Numbers.mun_power_nat (a := (2 : ℤ)) (by norm_num) (m := j + 1) (add_nonneg (hH1) (by norm_num)))
  -- 4. inequalities, from 2
  have s4 : (2 ^ j.toNat : ℤ) ≤ 2 ^ j.toNat * 2 := by linarith only [s2]
  -- 5. transitivity, from 4, 1
  have s5 : (2 ^ j.toNat : ℤ) ≤ 2 ^ (j + 1).toNat := by exact LE.le.trans_eq s4 s1.symm
  -- 6. proof
  -- what this block shows, Lean's types give
  -- 7. mun:sum-split a := 1, b := 2^j, c := 2^(j + 1), from 5, 6
  have r41_1 : (1 : ℤ) ≤ 2 ^ j.toNat + 1 := by linarith only [s2]
  have s7 : (∑ k ∈ Finset.Icc (1 : ℤ) (2 ^ (j + 1).toNat : ℤ), (1 / (k : ℚ) : ℚ)) = (∑ k ∈ Finset.Icc (1 : ℤ) (2 ^ j.toNat : ℤ), (1 / (k : ℚ) : ℚ)) + (∑ k ∈ Finset.Icc (2 ^ j.toNat + 1 : ℤ) (2 ^ (j + 1).toNat : ℤ), (1 / (k : ℚ) : ℚ)) := by exact (Parley.Items.Stdlib.Sums.mun_sum_split (t := (fun k : ℤ => 1 / (k : ℚ))) (a := (1 : ℤ)) (b := (2 ^ j.toNat : ℤ)) (c := (2 ^ (j + 1).toNat : ℤ)) r41_1 s5)
  -- 8. inequalities, from 2
  have s8 : (0 : ℤ) < 2 ^ j.toNat + 1 := by linarith only [s2]
  -- 9. proof
  have s9 : ∀ k : ℤ, k ∈ Finset.Icc (2 ^ j.toNat + 1) (2 ^ (j + 1).toNat) → 1 / 2 ^ (j + 1).toNat ≤ 1 / (k : ℚ) := by
    intro k hK2
    try push_cast at hK2
    try have hK2_bounds := Finset.mem_Icc.mp hK2
    -- 9.1. mun:range-bounds a := 2^j + 1, b := 2^(j + 1), from K2
    have s9_1a : 2 ^ j.toNat + 1 ≤ k := by exact (Parley.Items.Stdlib.Sums.mun_range_bounds_1 (a := (2 ^ j.toNat + 1 : ℤ)) (b := (2 ^ (j + 1).toNat : ℤ)) (k := k) hK2)
    have s9_1b : k ≤ 2 ^ (j + 1).toNat := by exact (Parley.Items.Stdlib.Sums.mun_range_bounds_2 (a := (2 ^ j.toNat + 1 : ℤ)) (b := (2 ^ (j + 1).toNat : ℤ)) (k := k) hK2)
    -- 9.2. transitivity, from 8, 9.1
    have s9_2 : k > 0 := by exact lt_of_lt_of_le s8 s9_1a
    -- 9.3. mun:reciprocal-order x := k, y := 2^(j + 1), from 9.1
    have r58_1 : k > 0 := by exact s9_2
    have r58_2 : (2 ^ (j + 1).toNat : ℤ) > 0 := by linarith only [s3]
    exact ((Parley.Items.Stdlib.Numbers.mun_reciprocal_order (x := (k : ℚ)) (by exact_mod_cast gt_iff_lt.mp r58_1) (y := (2 ^ (j + 1).toNat : ℚ)) (by exact_mod_cast gt_iff_lt.mp r58_2))).mp (by exact_mod_cast s9_1b)
  -- 10. proof
  -- what this block shows, Lean's types give
  -- 11. mun:sum-le a := 2^j + 1, b := 2^(j + 1), from 9
  have s11 : (∑ k ∈ Finset.Icc (2 ^ j.toNat + 1 : ℤ) (2 ^ (j + 1).toNat : ℤ), (1 / 2 ^ (j + 1).toNat : ℚ)) ≤ (∑ k ∈ Finset.Icc (2 ^ j.toNat + 1 : ℤ) (2 ^ (j + 1).toNat : ℤ), (1 / (k : ℚ) : ℚ)) := by exact (Parley.Items.Stdlib.Sums.mun_sum_le (t := (fun k : ℤ => (1 / 2 ^ (j + 1).toNat : ℚ))) (u := (fun k : ℤ => 1 / (k : ℚ))) (a := (2 ^ j.toNat + 1 : ℤ)) (b := (2 ^ (j + 1).toNat : ℤ)) s9)
  -- 12. inequalities, from 2
  have s12 : (2 ^ j.toNat + 1 : ℤ) ≤ 2 ^ j.toNat * 2 := by linarith only [s2]
  -- 13. transitivity, from 12, 1
  have s13 : (2 ^ j.toNat + 1 : ℤ) ≤ 2 ^ (j + 1).toNat := by exact LE.le.trans_eq s12 s1.symm
  -- 14. mun:sum-constant a := 2^j + 1, b := 2^(j + 1), c := 1/2^(j + 1)
  have r87_1 : (2 ^ j.toNat + 1 : ℤ) ≤ 2 ^ (j + 1).toNat := by exact s13
  have s14 : (∑ k ∈ Finset.Icc (2 ^ j.toNat + 1 : ℤ) (2 ^ (j + 1).toNat : ℤ), (1 / 2 ^ (j + 1).toNat : ℚ)) = (2 ^ (j + 1).toNat - (2 ^ j.toNat + 1) + 1) * (1 / 2 ^ (j + 1).toNat) := by
    have hI : (∑ k ∈ Finset.Icc (2 ^ j.toNat + 1 : ℤ) (2 ^ (j + 1).toNat : ℤ), (1 / 2 ^ (j + 1).toNat : ℚ)) = (2 ^ (j + 1).toNat - (2 ^ j.toNat + 1) + 1) * (1 / 2 ^ (j + 1).toNat) := by parley_instance ((Parley.Items.Stdlib.Sums.mun_sum_constant (a := (2 ^ j.toNat + 1 : ℤ)) (b := (2 ^ (j + 1).toNat : ℤ)) r87_1 (c := (1 / 2 ^ (j + 1).toNat : ℚ))))
    exact hI
  -- 15. calculation
  have s15 : ((2 ^ (j + 1).toNat - (2 ^ j.toNat + 1) + 1) * (1 / 2 ^ (j + 1).toNat) : ℚ) = 1 / 2 := by
    calc ((2 ^ (j + 1).toNat - (2 ^ j.toNat + 1) + 1) * (1 / 2 ^ (j + 1).toNat) : ℚ) = (2 ^ j.toNat * 2 - (2 ^ j.toNat + 1) + 1) * (1 / (2 ^ j.toNat * 2)) := by
          have e_w : (2 ^ (j + 1).toNat : ℚ) = 2 ^ j.toNat * 2 := by have h := congrArg (fun x : ℤ => (x : ℚ)) s1; push_cast at h; linear_combination (norm := parley_norm) h
          (have h := congrArg (fun t : ℚ => (t - (2 ^ j.toNat + 1) + 1) * (1 / t)) e_w; push_cast at h ⊢; all_goals exact_mod_cast h)
      _ = 1 / 2 := by parley_ring
  -- 16. transitivity, from 15, 14, 11
  have s16 : 1 / 2 ≤ (∑ k ∈ Finset.Icc (2 ^ j.toNat + 1 : ℤ) (2 ^ (j + 1).toNat : ℤ), (1 / (k : ℚ) : ℚ)) := by exact Eq.trans_le (Eq.trans s15.symm s14.symm) s11
  -- 17. inequalities
  have s17 : (∑ k ∈ Finset.Icc (1 : ℤ) (2 ^ j.toNat : ℤ), (1 / (k : ℚ) : ℚ)) + 1 / 2 ≤ (∑ k ∈ Finset.Icc (1 : ℤ) (2 ^ j.toNat : ℤ), (1 / (k : ℚ) : ℚ)) + (∑ k ∈ Finset.Icc (2 ^ j.toNat + 1 : ℤ) (2 ^ (j + 1).toNat : ℤ), (1 / (k : ℚ) : ℚ)) := by linarith only [s16]
  -- 18. transitivity, from 17, 7
  exact LE.le.trans_eq s17 s7.symm

end Parley.Proofs.Hammack.HarmonicLowerBound.HarmonicDoubling
