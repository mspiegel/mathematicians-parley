module

public import AlgebraTactics
public import Counting
public import FactorialTactics
public import OrderTactics
public import SubstTactics
public import Tactics
public import Mathlib.Algebra.Group.Even
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.Positivity.Basic
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
  have s1 : k ≤ n ∨ ¬ k ≤ n := by exact (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := k ≤ n))
  -- 2. cases, from 1
  rcases s1 with hC1 | hC2
  · skip
    -- 2.1. mun:nat-minus-one
    have s2_1 : 0 ≤ n - 1 := by exact (Parley.Items.Stdlib.Numbers.mun_nat_minus_one (n := n) (by parley_side))
    -- 2.2. inequalities, from C1, H2
    have s2_2a : 1 ≤ k := by parley_order
    have s2_2b : k ≤ n - 1 + 1 := by parley_order
    -- 2.3. def:range n := (n − 1) + 1, from 2.2
    have s2_3 : k ∈ Finset.Icc (1 : ℤ) (n - 1 + 1) := ((Parley.Items.Stdlib.Sums.def_range (k := k) (n := n - 1 + 1))).mpr (by parley_side)
    -- 2.4. thm:weighted-term m := n − 1, from 2.3
    have r78_1 : 0 ≤ n - 1 := by parley_side
    have s2_4 : k * (LeanBridges.Counting.choose (n - 1 + 1) k : ℤ) = (n - 1 + 1) * (LeanBridges.Counting.choose (n - 1) (k - 1) : ℤ) := by exact (Parley.Proofs.Hammack.WeightedBinomialSum.WeightedTerm.weighted_term (m := n - 1) (by parley_side) (k := k) s2_3)
    -- 2.5. substitute
    have s2_5 : k * (LeanBridges.Counting.choose n k : ℤ) = n * (LeanBridges.Counting.choose (n - 1) (k - 1) : ℤ) := by
      have c1 : n - 1 + 1 = n := by parley_ring
      have row1 : k * (LeanBridges.Counting.choose n k : ℤ) = n * (LeanBridges.Counting.choose (n - 1) (k - 1) : ℤ) := by parley_subst_at c1 s2_4
      exact row1
    -- 2.6. mun:binomial-nat0 n := n − 1, k := k − 1
    have r87_1 : 0 ≤ n - 1 := by parley_side
    have s2_6 : 0 ≤ (LeanBridges.Counting.choose (n - 1) (k - 1) : ℤ) := by exact (Parley.Items.Stdlib.Counting.mun_binomial_nat0 (n := n - 1) (by parley_side) (k := k - 1))
    -- 2.7. thm:even-times A := n, B := C(n − 1, k − 1), from H3
    have s2_7 : Even (n * (LeanBridges.Counting.choose (n - 1) (k - 1) : ℤ)) := by exact (Parley.Proofs.Hammack.BinomialEvenForOddK.EvenTimes.even_times (A := n) (B := (LeanBridges.Counting.choose (n - 1) (k - 1) : ℤ)) hH3)
    -- 2.8. substitute k·C(n, k) = n·C(n − 1, k − 1) (line 2.5) into line 2.7
    have s2_8 : Even (k * (LeanBridges.Counting.choose n k : ℤ)) := by (have h := Eq.subst (motive := (fun t : ℤ => Even t)) (s2_5).symm s2_7; push_cast at h ⊢; all_goals exact_mod_cast h)
    -- 2.9. thm:odd-factor A := k, B := C(n, k), from H4, 2.8
    exact (Parley.Proofs.Hammack.BinomialEvenForOddK.OddFactor.odd_factor (A := k) (B := (LeanBridges.Counting.choose n k : ℤ)) hH4 s2_8)
  · skip
    -- 2.10. inequalities, from C2
    have s2_10 : n < k := by parley_order
    -- 2.11. def:C, from 2.10
    have s2_11 : (LeanBridges.Counting.choose n k : ℤ) = 0 := by exact (Parley.Items.Stdlib.Counting.def_C_3 (n := n) (by parley_side) (k := k)) s2_10
    -- 2.12. calculation
    have s2_12 : (LeanBridges.Counting.choose n k : ℤ) = 2 * 0 := by
      calc (LeanBridges.Counting.choose n k : ℤ) = 0 := by exact s2_11
        _ = 2 * 0 := by norm_num
    -- 2.13. def:even n := C(n, k), from 2.12
    exact ((Parley.Items.Stdlib.Divisibility.def_even (n := (LeanBridges.Counting.choose n k : ℤ)))).mpr ⟨(0 : ℤ), s2_12⟩

end Parley.Proofs.Hammack.BinomialEvenForOddK.BinomialEvenForOddK
