module

public import AlgebraTactics
public import Counting
public import FactorialTactics
public import NormTactics
public import OrderTactics
public import SubstTactics
public import Tactics
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Rat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Qify
public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Sums

/-! Written from proofs/hammack/weighted-binomial-sum.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.WeightedBinomialSum.WeightedTerm

set_option maxHeartbeats 400000 in
theorem weighted_term (m : ℤ) (hH1 : 0 ≤ m) (k : ℤ) (hH2 : k ∈ Finset.Icc (1 : ℤ) (m + 1)) :
    k * (LeanBridges.Counting.choose (m + 1) k : ℤ) = (m + 1) * (LeanBridges.Counting.choose m (k - 1) : ℤ) := by
  -- 1. mun:range-bounds a := 1, b := m + 1, from H2
  have s1a : 1 ≤ k := by exact (Parley.Items.Stdlib.Sums.mun_range_bounds_1 (a := (1 : ℤ)) (b := m + 1) (k := k) hH2)
  have s1b : k ≤ m + 1 := by exact (Parley.Items.Stdlib.Sums.mun_range_bounds_2 (a := (1 : ℤ)) (b := m + 1) (k := k) hH2)
  -- 2. inequalities, from 1
  have s2a : k > 0 := by parley_order
  have s2b : 0 ≤ k := by parley_order
  have s2c : k ≤ m + 1 := by parley_order
  -- 3. def:range-between a := 0, b := m + 1, from 2
  have s3 : k ∈ Finset.Icc (0 : ℤ) (m + 1) := ((Parley.Items.Stdlib.Sums.def_range_between (k := k) (a := (0 : ℤ)) (b := m + 1))).mpr (by parley_side)
  -- 4. def:C n := m + 1, from 3
  have s4 : (LeanBridges.Counting.choose (m + 1) k : ℚ) = (LeanBridges.Counting.factorial (m + 1) : ℚ) / ((LeanBridges.Counting.factorial (m + 1 - k) : ℚ) * (LeanBridges.Counting.factorial k : ℚ)) := by exact (Parley.Items.Stdlib.Counting.def_C_2 (n := m + 1) (by parley_side) (k := k)) s3
  -- 5. inequalities, from 1
  have s5a : 0 ≤ k - 1 := by parley_order
  have s5b : k - 1 ≤ m := by parley_order
  -- 6. def:range-between k := k − 1, a := 0, b := m, from 5
  have s6 : k - 1 ∈ Finset.Icc (0 : ℤ) m := ((Parley.Items.Stdlib.Sums.def_range_between (k := k - 1) (a := (0 : ℤ)) (b := m))).mpr (by parley_side)
  -- 7. algebra
  have s7 : m - (k - 1) = m + 1 - k := by parley_ring
  -- 8. substitute m − (k − 1) = (m + 1) − k (line 7)
  have s8 : (LeanBridges.Counting.factorial (m - (k - 1)) : ℤ) = (LeanBridges.Counting.factorial (m + 1 - k) : ℤ) := by parley_subst s7
  -- 9. def:factorial n := m
  have s9 : (LeanBridges.Counting.factorial (m + 1) : ℤ) = (LeanBridges.Counting.factorial m : ℤ) * (m + 1) := by exact (Parley.Items.Stdlib.Counting.def_factorial_3 (n := m) (by parley_side))
  -- 10. def:factorial n := k − 1
  have r49_1 : 0 ≤ k - 1 := by exact (Parley.Items.Stdlib.Numbers.mun_nat_minus_one (n := k) (by parley_side))
  have s10 : (LeanBridges.Counting.factorial (k - 1 + 1) : ℤ) = (LeanBridges.Counting.factorial (k - 1) : ℤ) * (k - 1 + 1) := by exact (Parley.Items.Stdlib.Counting.def_factorial_3 (n := k - 1) (by parley_side))
  -- 11. substitute
  have s11 : (LeanBridges.Counting.factorial k : ℤ) = (LeanBridges.Counting.factorial (k - 1) : ℤ) * k := by
    have c1 : k - 1 + 1 = k := by parley_ring
    have row1 : (LeanBridges.Counting.factorial k : ℤ) = (LeanBridges.Counting.factorial (k - 1) : ℤ) * k := by parley_subst_at c1 s10
    exact row1
  -- 12. mun:range-difference a := 1, n := m + 1, from H2
  have s12 : 0 ≤ m + 1 - k := by exact (Parley.Items.Stdlib.Sums.mun_range_difference (a := (1 : ℤ)) (n := m + 1) (k := k) hH2)
  -- 13. mun:factorial-nat n := (m + 1) − k, from 12
  have s13 : 0 < (LeanBridges.Counting.factorial (m + 1 - k) : ℤ) := by exact (Parley.Items.Stdlib.Counting.mun_factorial_nat (n := m + 1 - k) (by parley_side))
  -- 14. mun:factorial-nat n := k − 1
  have r64_1 : 0 ≤ k - 1 := by exact (Parley.Items.Stdlib.Numbers.mun_nat_minus_one (n := k) (by parley_side))
  have s14 : 0 < (LeanBridges.Counting.factorial (k - 1) : ℤ) := by exact (Parley.Items.Stdlib.Counting.mun_factorial_nat (n := k - 1) (by parley_side))
  -- 15. calculation
  have s15 : (LeanBridges.Counting.choose m (k - 1) : ℚ) = (LeanBridges.Counting.factorial m : ℚ) / ((LeanBridges.Counting.factorial (m + 1 - k) : ℚ) * (LeanBridges.Counting.factorial (k - 1) : ℚ)) := by
    calc (LeanBridges.Counting.choose m (k - 1) : ℚ) = (LeanBridges.Counting.factorial m : ℚ) / ((LeanBridges.Counting.factorial (m - (k - 1)) : ℚ) * (LeanBridges.Counting.factorial (k - 1) : ℚ)) := by exact (Parley.Items.Stdlib.Counting.def_C_2 (n := m) (by parley_side) (k := k - 1)) s6
      _ = (LeanBridges.Counting.factorial m : ℚ) / ((LeanBridges.Counting.factorial (m + 1 - k) : ℚ) * (LeanBridges.Counting.factorial (k - 1) : ℚ)) := by
          have s8_w : (LeanBridges.Counting.factorial (m - (k - 1)) : ℚ) = (LeanBridges.Counting.factorial (m + 1 - k) : ℚ) := by have h := congrArg (fun x : ℤ => (x : ℚ)) s8; push_cast at h; linear_combination (norm := parley_norm) h
          first | parley_subst s8_w | parley_subst s8
  -- 16. calculation
  try qify
  calc (k : ℚ) * (LeanBridges.Counting.choose (m + 1) k : ℚ) = (k : ℚ) * ((LeanBridges.Counting.factorial (m + 1) : ℚ) / ((LeanBridges.Counting.factorial (m + 1 - k) : ℚ) * (LeanBridges.Counting.factorial k : ℚ))) := by parley_subst s4
    _ = (k : ℚ) * ((LeanBridges.Counting.factorial m : ℚ) * ((m : ℚ) + 1) / ((LeanBridges.Counting.factorial (m + 1 - k) : ℚ) * (LeanBridges.Counting.factorial k : ℚ))) := by
        have s9_w : (LeanBridges.Counting.factorial (m + 1) : ℚ) = (LeanBridges.Counting.factorial m : ℚ) * ((m : ℚ) + 1) := by have h := congrArg (fun x : ℤ => (x : ℚ)) s9; push_cast at h; linear_combination (norm := parley_norm) h
        first | parley_subst s9_w | parley_subst s9
    _ = (k : ℚ) * ((LeanBridges.Counting.factorial m : ℚ) * ((m : ℚ) + 1) / ((LeanBridges.Counting.factorial (m + 1 - k) : ℚ) * ((LeanBridges.Counting.factorial (k - 1) : ℚ) * (k : ℚ)))) := by
        have s11_w : (LeanBridges.Counting.factorial k : ℚ) = (LeanBridges.Counting.factorial (k - 1) : ℚ) * (k : ℚ) := by have h := congrArg (fun x : ℤ => (x : ℚ)) s11; push_cast at h; linear_combination (norm := parley_norm) h
        first | parley_subst s11_w | parley_subst s11
    _ = ((m : ℚ) + 1) * ((LeanBridges.Counting.factorial m : ℚ) / ((LeanBridges.Counting.factorial (m + 1 - k) : ℚ) * (LeanBridges.Counting.factorial (k - 1) : ℚ))) := by parley_ring
    _ = ((m : ℚ) + 1) * (LeanBridges.Counting.choose m (k - 1) : ℚ) := by parley_subst s15

end Parley.Proofs.Hammack.WeightedBinomialSum.WeightedTerm
