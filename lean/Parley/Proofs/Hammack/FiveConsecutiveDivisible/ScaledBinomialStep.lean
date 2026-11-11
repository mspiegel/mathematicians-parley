module

public import Counting
public import FactorialTactics
public import NormTactics
public import OrderTactics
public import Tactics
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Sums
public import Parley.Proofs.Hammack.WeightedBinomialSum.WeightedTerm

/-! Written from proofs/hammack/five-consecutive-divisible.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.FiveConsecutiveDivisible.ScaledBinomialStep

theorem scaled_binomial_step (m : ℤ) (hH1 : 0 ≤ m) (i : ℤ) (hH2 : 0 ≤ i) (j : ℤ) (hH3 : 0 < j) (hH4 : j - 1 = i) :
    j * (LeanBridges.Counting.choose (m + j) j : ℤ) = (m + j) * (LeanBridges.Counting.choose (m + i) i : ℤ) := by
  -- 1. inequalities
  have s1 : j = i + 1 := by parley_side
  -- 2. inequalities, from H1
  have s2 : i + 1 ≤ m + i + 1 := by parley_order
  -- 3. transitivity, from 1, 2
  have s3 : j ≤ m + i + 1 := by parley_order
  -- 4. def:range-between k := j, a := 1, b := (m + i) + 1, from 3
  have r33_1 : 1 ≤ j := by parley_order
  have s4 : j ∈ Finset.Icc (1 : ℤ) (m + i + 1) := ((Parley.Items.Stdlib.Sums.def_range_between (k := j) (a := (1 : ℤ)) (b := m + i + 1))).mpr ⟨r33_1, s3⟩
  -- 5. thm:weighted-term m := m + i, k := j, from 4
  have s5 : j * (LeanBridges.Counting.choose (m + i + 1) j : ℤ) = (m + i + 1) * (LeanBridges.Counting.choose (m + i) (j - 1) : ℤ) := by exact (Parley.Proofs.Hammack.WeightedBinomialSum.WeightedTerm.weighted_term (m := m + i) (by parley_side) (k := j) s4)
  -- 6. substitute j − 1 = i (H4) into line 5
  have s6 : j * (LeanBridges.Counting.choose (m + i + 1) j : ℤ) = (m + i + 1) * (LeanBridges.Counting.choose (m + i) i : ℤ) := by (have h := Eq.subst (motive := (fun t : ℤ => j * (LeanBridges.Counting.choose (m + i + 1) j : ℤ) = (m + i + 1) * (LeanBridges.Counting.choose (m + i) t : ℤ))) hH4 s5; push_cast at h ⊢; all_goals exact_mod_cast h)
  -- 7. algebra, from 1
  have s7 : m + i + 1 = m + j := by linear_combination (norm := parley_norm) (-1) * s1
  -- 8. substitute (m + i) + 1 = m + j (line 7) into line 6
  (have h := Eq.subst (motive := (fun t : ℤ => j * (LeanBridges.Counting.choose t j : ℤ) = t * (LeanBridges.Counting.choose (m + i) i : ℤ))) s7 s6; push_cast at h ⊢; all_goals exact_mod_cast h)

end Parley.Proofs.Hammack.FiveConsecutiveDivisible.ScaledBinomialStep
