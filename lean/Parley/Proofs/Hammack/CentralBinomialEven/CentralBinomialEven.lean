module

public import AlgebraTactics
public import Counting
public import FactorialTactics
public import OrderTactics
public import PowerTactics
public import SubstTactics
public import Tactics
public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Sums
public import Parley.Proofs.Hammack.WeightedBinomialSum.WeightedTerm

/-! Written from proofs/hammack/central-binomial-even.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.CentralBinomialEven.CentralBinomialEven

theorem central_binomial_even (n : ℤ) (hH1 : 0 < n) :
    Even (LeanBridges.Counting.choose (2 * n) n : ℤ) := by
  -- 1. mun:nat-minus-one n := 2n
  have s1 : 0 ≤ 2 * n - 1 := by first | exact (Parley.Items.Stdlib.Numbers.mun_nat_minus_one (n := 2 * n) (by parley_side)) | exact ((Parley.Items.Stdlib.Numbers.mun_nat_minus_one (n := 2 * n) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_nat_minus_one (n := 2 * n) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_nat_minus_one (n := 2 * n) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_nat_minus_one (n := 2 * n) (by parley_side)); parley_side)
  -- 2. inequalities, from H1
  have s2 : 1 ≤ n := by parley_order
  -- 3. inequalities, from H1
  have s3 : n ≤ 2 * n - 1 + 1 := by parley_order
  -- 4. def:range-between k := n, a := 1, b := (2n − 1) + 1, from 2, 3
  have s4 : n ∈ Finset.Icc (1 : ℤ) (2 * n - 1 + 1) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sums.def_range_between (k := n) (a := (1 : ℤ)) (b := 2 * n - 1 + 1))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Sums.def_range_between (k := n) (a := (1 : ℤ)) (b := 2 * n - 1 + 1))).mpr (by parley_side); parley_side)
  -- 5. thm:weighted-term m := 2n − 1, k := n, from 1, 4
  have s5 : n * (LeanBridges.Counting.choose (2 * n - 1 + 1) n : ℤ) = (2 * n - 1 + 1) * (LeanBridges.Counting.choose (2 * n - 1) (n - 1) : ℤ) := by first | linear_combination (norm := parley_norm) (Parley.Proofs.Hammack.WeightedBinomialSum.WeightedTerm.weighted_term (m := 2 * n - 1) (by parley_side) (k := n) s4) | (have h := (Parley.Proofs.Hammack.WeightedBinomialSum.WeightedTerm.weighted_term (m := 2 * n - 1) (by parley_side) (k := n) s4); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Hammack.WeightedBinomialSum.WeightedTerm.weighted_term (m := 2 * n - 1) (by parley_side) (k := n) s4); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Proofs.Hammack.WeightedBinomialSum.WeightedTerm.weighted_term (m := 2 * n - 1) (by parley_side) (k := n) s4) | exact_mod_cast ((Parley.Proofs.Hammack.WeightedBinomialSum.WeightedTerm.weighted_term (m := 2 * n - 1) (by parley_side) (k := n) s4)).symm | (have h := (Parley.Proofs.Hammack.WeightedBinomialSum.WeightedTerm.weighted_term (m := 2 * n - 1) (by parley_side) (k := n) s4); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Hammack.WeightedBinomialSum.WeightedTerm.weighted_term (m := 2 * n - 1) (by parley_side) (k := n) s4); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Hammack.WeightedBinomialSum.WeightedTerm.weighted_term (m := 2 * n - 1) (by parley_side) (k := n) s4); parley_int_power h) | (have h := (Parley.Proofs.Hammack.WeightedBinomialSum.WeightedTerm.weighted_term (m := 2 * n - 1) (by parley_side) (k := n) s4); parley_side)
  -- 6. substitute
  have s6 : n * (LeanBridges.Counting.choose (2 * n) n : ℤ) = 2 * n * (LeanBridges.Counting.choose (2 * n - 1) (n - 1) : ℤ) := by
    have c1 : 2 * n - 1 + 1 = 2 * n := by parley_ring
    have row1 : n * (LeanBridges.Counting.choose (2 * n) n : ℤ) = 2 * n * (LeanBridges.Counting.choose (2 * n - 1) (n - 1) : ℤ) := by parley_subst_at c1 s5
    exact row1
  -- 7. mun:binomial-nat0 n := 2n − 1, k := n − 1, from 1
  have s7 : 0 ≤ (LeanBridges.Counting.choose (2 * n - 1) (n - 1) : ℤ) := by first | exact (Parley.Items.Stdlib.Counting.mun_binomial_nat0 (n := 2 * n - 1) (by parley_side) (k := n - 1)) | exact ((Parley.Items.Stdlib.Counting.mun_binomial_nat0 (n := 2 * n - 1) (by parley_side) (k := n - 1))).symm | simpa using (Parley.Items.Stdlib.Counting.mun_binomial_nat0 (n := 2 * n - 1) (by parley_side) (k := n - 1)) | exact_mod_cast (Parley.Items.Stdlib.Counting.mun_binomial_nat0 (n := 2 * n - 1) (by parley_side) (k := n - 1)) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_nat0 (n := 2 * n - 1) (by parley_side) (k := n - 1)); parley_side)
  -- 8. algebra, from 6
  have s8 : (LeanBridges.Counting.choose (2 * n) n : ℤ) * n = 2 * (LeanBridges.Counting.choose (2 * n - 1) (n - 1) : ℤ) * n := by linear_combination (norm := parley_norm) s6
  -- 9. mun:multiply-cancel a := C(2n, n), b := 2·C(2n − 1, n − 1), c := n, from H1, 8
  have s9 : (LeanBridges.Counting.choose (2 * n) n : ℤ) = 2 * (LeanBridges.Counting.choose (2 * n - 1) (n - 1) : ℤ) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := (LeanBridges.Counting.choose (2 * n) n : ℤ)) (b := 2 * (LeanBridges.Counting.choose (2 * n - 1) (n - 1) : ℤ)) (c := n) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := (LeanBridges.Counting.choose (2 * n) n : ℤ)) (b := 2 * (LeanBridges.Counting.choose (2 * n - 1) (n - 1) : ℤ)) (c := n) (by parley_side) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := (LeanBridges.Counting.choose (2 * n) n : ℤ)) (b := 2 * (LeanBridges.Counting.choose (2 * n - 1) (n - 1) : ℤ)) (c := n) (by parley_side) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := (LeanBridges.Counting.choose (2 * n) n : ℤ)) (b := 2 * (LeanBridges.Counting.choose (2 * n - 1) (n - 1) : ℤ)) (c := n) (by parley_side) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := (LeanBridges.Counting.choose (2 * n) n : ℤ)) (b := 2 * (LeanBridges.Counting.choose (2 * n - 1) (n - 1) : ℤ)) (c := n) (by parley_side) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := (LeanBridges.Counting.choose (2 * n) n : ℤ)) (b := 2 * (LeanBridges.Counting.choose (2 * n - 1) (n - 1) : ℤ)) (c := n) (by parley_side) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := (LeanBridges.Counting.choose (2 * n) n : ℤ)) (b := 2 * (LeanBridges.Counting.choose (2 * n - 1) (n - 1) : ℤ)) (c := n) (by parley_side) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := (LeanBridges.Counting.choose (2 * n) n : ℤ)) (b := 2 * (LeanBridges.Counting.choose (2 * n - 1) (n - 1) : ℤ)) (c := n) (by parley_side) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := (LeanBridges.Counting.choose (2 * n) n : ℤ)) (b := 2 * (LeanBridges.Counting.choose (2 * n - 1) (n - 1) : ℤ)) (c := n) (by parley_side) (by parley_side)); parley_side)
  -- 10. def:even n := C(2n, n), from 9
  have s10 : Even (LeanBridges.Counting.choose (2 * n) n : ℤ) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_even (n := (LeanBridges.Counting.choose (2 * n) n : ℤ)))).mpr ⟨(LeanBridges.Counting.choose (2 * n - 1) (n - 1) : ℤ), by parley_side⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_even (n := (LeanBridges.Counting.choose (2 * n) n : ℤ)))).mpr ⟨(LeanBridges.Counting.choose (2 * n - 1) (n - 1) : ℤ), by parley_side⟩; parley_side)
  all_goals exact s10

end Parley.Proofs.Hammack.CentralBinomialEven.CentralBinomialEven
