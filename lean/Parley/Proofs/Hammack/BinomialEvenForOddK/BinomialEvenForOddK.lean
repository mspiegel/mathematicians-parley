module

public import AlgebraTactics
public import Counting
public import FactorialTactics
public import OrderTactics
public import PowerTactics
public import SubstTactics
public import Tactics
public import Mathlib.Algebra.Group.Even
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Int.Notation
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Reasoning
public import Parley.Items.Stdlib.Sums
public import Parley.Proofs.Hammack.BinomialEvenForOddK.EvenTimes
public import Parley.Proofs.Hammack.BinomialEvenForOddK.OddFactor
public import Parley.Proofs.Hammack.WeightedBinomialSum.WeightedTerm

/-! Written from proofs/hammack/binomial-even-for-odd-k.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.BinomialEvenForOddK.BinomialEvenForOddK

set_option maxHeartbeats 400000 in
theorem binomial_even_for_odd_k (n : ℤ) (hH1 : 0 < n) (k : ℤ) (hH2 : 0 < k) (hH3 : Even n) (hH4 : Odd k) :
    Even (LeanBridges.Counting.choose n k : ℤ) := by
  -- 1. axi:excluded-middle P := k ≤ n
  have s1 : k ≤ n ∨ ¬ k ≤ n := by first | exact (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := k ≤ n)) | exact ((Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := k ≤ n))).symm | simpa using (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := k ≤ n)) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := k ≤ n)) | (have h := (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := k ≤ n)); parley_side)
  -- 2. cases, from 1
  have s2 : Even (LeanBridges.Counting.choose n k : ℤ) := by
    rcases s1 with hC1 | hC2
    · skip
      -- 2.1. mun:nat-minus-one
      have s2_1 : 0 ≤ n - 1 := by first | exact (Parley.Items.Stdlib.Numbers.mun_nat_minus_one (n := n) (by parley_side)) | exact ((Parley.Items.Stdlib.Numbers.mun_nat_minus_one (n := n) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_nat_minus_one (n := n) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_nat_minus_one (n := n) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_nat_minus_one (n := n) (by parley_side)); parley_side)
      -- 2.2. inequalities, from C1, H2
      have s2_2a : 1 ≤ k := by parley_order
      have s2_2b : k ≤ n - 1 + 1 := by parley_order
      -- 2.3. def:range n := (n − 1) + 1, from 2.2
      have s2_3 : k ∈ Finset.Icc (1 : ℤ) (n - 1 + 1) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sums.def_range (k := k) (n := n - 1 + 1))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Sums.def_range (k := k) (n := n - 1 + 1))).mpr (by parley_side); parley_side)
      -- 2.4. thm:weighted-term m := n − 1, from 2.3
      have r78_1 : 0 ≤ n - 1 := by parley_side
      have s2_4 : k * (LeanBridges.Counting.choose (n - 1 + 1) k : ℤ) = (n - 1 + 1) * (LeanBridges.Counting.choose (n - 1) (k - 1) : ℤ) := by first | linear_combination (norm := parley_norm) (Parley.Proofs.Hammack.WeightedBinomialSum.WeightedTerm.weighted_term (m := n - 1) (by parley_side) (k := k) s2_3) | (have h := (Parley.Proofs.Hammack.WeightedBinomialSum.WeightedTerm.weighted_term (m := n - 1) (by parley_side) (k := k) s2_3); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Hammack.WeightedBinomialSum.WeightedTerm.weighted_term (m := n - 1) (by parley_side) (k := k) s2_3); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Proofs.Hammack.WeightedBinomialSum.WeightedTerm.weighted_term (m := n - 1) (by parley_side) (k := k) s2_3) | exact_mod_cast ((Parley.Proofs.Hammack.WeightedBinomialSum.WeightedTerm.weighted_term (m := n - 1) (by parley_side) (k := k) s2_3)).symm | (have h := (Parley.Proofs.Hammack.WeightedBinomialSum.WeightedTerm.weighted_term (m := n - 1) (by parley_side) (k := k) s2_3); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Hammack.WeightedBinomialSum.WeightedTerm.weighted_term (m := n - 1) (by parley_side) (k := k) s2_3); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Hammack.WeightedBinomialSum.WeightedTerm.weighted_term (m := n - 1) (by parley_side) (k := k) s2_3); parley_int_power h) | (have h := (Parley.Proofs.Hammack.WeightedBinomialSum.WeightedTerm.weighted_term (m := n - 1) (by parley_side) (k := k) s2_3); parley_side)
      -- 2.5. substitute
      have s2_5 : k * (LeanBridges.Counting.choose n k : ℤ) = n * (LeanBridges.Counting.choose (n - 1) (k - 1) : ℤ) := by
        have c1 : n - 1 + 1 = n := by parley_ring
        have row1 : k * (LeanBridges.Counting.choose n k : ℤ) = n * (LeanBridges.Counting.choose (n - 1) (k - 1) : ℤ) := by parley_subst_at c1 s2_4
        exact row1
      -- 2.6. mun:binomial-nat0 n := n − 1, k := k − 1
      have r87_1 : 0 ≤ n - 1 := by parley_side
      have s2_6 : 0 ≤ (LeanBridges.Counting.choose (n - 1) (k - 1) : ℤ) := by first | exact (Parley.Items.Stdlib.Counting.mun_binomial_nat0 (n := n - 1) (by parley_side) (k := k - 1)) | exact ((Parley.Items.Stdlib.Counting.mun_binomial_nat0 (n := n - 1) (by parley_side) (k := k - 1))).symm | simpa using (Parley.Items.Stdlib.Counting.mun_binomial_nat0 (n := n - 1) (by parley_side) (k := k - 1)) | exact_mod_cast (Parley.Items.Stdlib.Counting.mun_binomial_nat0 (n := n - 1) (by parley_side) (k := k - 1)) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_nat0 (n := n - 1) (by parley_side) (k := k - 1)); parley_side)
      -- 2.7. thm:even-times A := n, B := C(n − 1, k − 1), from H3
      have s2_7 : Even (n * (LeanBridges.Counting.choose (n - 1) (k - 1) : ℤ)) := by first | exact (Parley.Proofs.Hammack.BinomialEvenForOddK.EvenTimes.even_times (A := n) (B := (LeanBridges.Counting.choose (n - 1) (k - 1) : ℤ)) hH3) | exact ((Parley.Proofs.Hammack.BinomialEvenForOddK.EvenTimes.even_times (A := n) (B := (LeanBridges.Counting.choose (n - 1) (k - 1) : ℤ)) hH3)).symm | simpa using (Parley.Proofs.Hammack.BinomialEvenForOddK.EvenTimes.even_times (A := n) (B := (LeanBridges.Counting.choose (n - 1) (k - 1) : ℤ)) hH3) | exact_mod_cast (Parley.Proofs.Hammack.BinomialEvenForOddK.EvenTimes.even_times (A := n) (B := (LeanBridges.Counting.choose (n - 1) (k - 1) : ℤ)) hH3) | (have h := (Parley.Proofs.Hammack.BinomialEvenForOddK.EvenTimes.even_times (A := n) (B := (LeanBridges.Counting.choose (n - 1) (k - 1) : ℤ)) hH3); parley_side)
      -- 2.8. substitute k·C(n, k) = n·C(n − 1, k − 1) (line 2.5) into line 2.7
      have s2_8 : Even (k * (LeanBridges.Counting.choose n k : ℤ)) := by parley_subst_at s2_5 s2_7
      -- 2.9. thm:odd-factor A := k, B := C(n, k), from H4, 2.8
      have s2_9 : Even (LeanBridges.Counting.choose n k : ℤ) := by first | exact (Parley.Proofs.Hammack.BinomialEvenForOddK.OddFactor.odd_factor (A := k) (B := (LeanBridges.Counting.choose n k : ℤ)) hH4 s2_8) | exact ((Parley.Proofs.Hammack.BinomialEvenForOddK.OddFactor.odd_factor (A := k) (B := (LeanBridges.Counting.choose n k : ℤ)) hH4 s2_8)).symm | simpa using (Parley.Proofs.Hammack.BinomialEvenForOddK.OddFactor.odd_factor (A := k) (B := (LeanBridges.Counting.choose n k : ℤ)) hH4 s2_8) | exact_mod_cast (Parley.Proofs.Hammack.BinomialEvenForOddK.OddFactor.odd_factor (A := k) (B := (LeanBridges.Counting.choose n k : ℤ)) hH4 s2_8) | (have h := (Parley.Proofs.Hammack.BinomialEvenForOddK.OddFactor.odd_factor (A := k) (B := (LeanBridges.Counting.choose n k : ℤ)) hH4 s2_8); parley_side)
      all_goals parley_side
    · skip
      -- 2.10. inequalities, from C2
      have s2_10 : n < k := by parley_order
      -- 2.11. def:C, from 2.10
      have s2_11 : (LeanBridges.Counting.choose n k : ℤ) = 0 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.def_C_3 (n := n) (by parley_side) (k := k)) (by parley_side) | (have h := (Parley.Items.Stdlib.Counting.def_C_3 (n := n) (by parley_side) (k := k)) (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_C_3 (n := n) (by parley_side) (k := k)) (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Counting.def_C_3 (n := n) (by parley_side) (k := k)) (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Counting.def_C_3 (n := n) (by parley_side) (k := k)) (by parley_side)).symm | (have h := (Parley.Items.Stdlib.Counting.def_C_3 (n := n) (by parley_side) (k := k)) (by parley_side); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_C_3 (n := n) (by parley_side) (k := k)) (by parley_side); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_C_3 (n := n) (by parley_side) (k := k)) (by parley_side); parley_int_power h) | (have h := (Parley.Items.Stdlib.Counting.def_C_3 (n := n) (by parley_side) (k := k)) (by parley_side); parley_side)
      -- 2.12. calculation
      have s2_12 : (LeanBridges.Counting.choose n k : ℤ) = 2 * 0 := by
        calc (LeanBridges.Counting.choose n k : ℤ) = 0 := by parley_side
          _ = 2 * 0 := by norm_num
      -- 2.13. def:even n := C(n, k), from 2.12
      have s2_13 : Even (LeanBridges.Counting.choose n k : ℤ) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_even (n := (LeanBridges.Counting.choose n k : ℤ)))).mpr ⟨(0 : ℤ), by parley_side⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_even (n := (LeanBridges.Counting.choose n k : ℤ)))).mpr ⟨(0 : ℤ), by parley_side⟩; parley_side)
      all_goals parley_side
  all_goals exact s2

end Parley.Proofs.Hammack.BinomialEvenForOddK.BinomialEvenForOddK
