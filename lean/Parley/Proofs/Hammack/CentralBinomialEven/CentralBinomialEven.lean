module

public import AlgebraTactics
public import Counting
public import FactorialTactics
public import NormTactics
public import Tactics
public import Mathlib.Algebra.Group.Even
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.Positivity.Basic
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
  have s1 : 0 ≤ 2 * n - 1 := by exact (Parley.Items.Stdlib.Numbers.mun_nat_minus_one (n := 2 * n) (mul_pos (by norm_num) (hH1)))
  -- 2. inequalities, from H1
  have s2 : 1 ≤ n := by linarith only [hH1]
  -- 3. inequalities, from H1
  have s3 : n ≤ 2 * n - 1 + 1 := by linarith only [hH1]
  -- 4. def:range-between k := n, a := 1, b := (2n − 1) + 1, from 2, 3
  have s4 : n ∈ Finset.Icc (1 : ℤ) (2 * n - 1 + 1) := ((Parley.Items.Stdlib.Sums.def_range_between (k := n) (a := (1 : ℤ)) (b := 2 * n - 1 + 1))).mpr ⟨s2, s3⟩
  -- 5. thm:weighted-term m := 2n − 1, k := n, from 1, 4
  have s5 : n * (LeanBridges.Counting.choose (2 * n - 1 + 1) n : ℤ) = (2 * n - 1 + 1) * (LeanBridges.Counting.choose (2 * n - 1) (n - 1) : ℤ) := by exact (Parley.Proofs.Hammack.WeightedBinomialSum.WeightedTerm.weighted_term (m := 2 * n - 1) s1 (k := n) s4)
  -- 6. substitute
  have s6 : n * (LeanBridges.Counting.choose (2 * n) n : ℤ) = 2 * n * (LeanBridges.Counting.choose (2 * n - 1) (n - 1) : ℤ) := by
    have c1 : 2 * n - 1 + 1 = 2 * n := by parley_ring
    have row1 : n * (LeanBridges.Counting.choose (2 * n) n : ℤ) = 2 * n * (LeanBridges.Counting.choose (2 * n - 1) (n - 1) : ℤ) := by (have h := Eq.subst (motive := (fun t : ℤ => n * (LeanBridges.Counting.choose t n : ℤ) = t * (LeanBridges.Counting.choose (2 * n - 1) (n - 1) : ℤ))) c1 s5; push_cast at h ⊢; all_goals exact_mod_cast h)
    exact row1
  -- 7. mun:binomial-nat0 n := 2n − 1, k := n − 1, from 1
  have s7 : 0 ≤ (LeanBridges.Counting.choose (2 * n - 1) (n - 1) : ℤ) := by exact (Parley.Items.Stdlib.Counting.mun_binomial_nat0 (n := 2 * n - 1) s1 (k := n - 1))
  -- 8. algebra, from 6
  have s8 : (LeanBridges.Counting.choose (2 * n) n : ℤ) * n = 2 * (LeanBridges.Counting.choose (2 * n - 1) (n - 1) : ℤ) * n := by linear_combination (norm := parley_norm) s6
  -- 9. mun:multiply-cancel a := C(2n, n), b := 2·C(2n − 1, n − 1), c := n, from H1, 8
  have s9 : (LeanBridges.Counting.choose (2 * n) n : ℤ) = 2 * (LeanBridges.Counting.choose (2 * n - 1) (n - 1) : ℤ) := by exact (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := (LeanBridges.Counting.choose (2 * n) n : ℤ)) (b := 2 * (LeanBridges.Counting.choose (2 * n - 1) (n - 1) : ℤ)) (c := n) (by parley_side) hH1.ne')
  -- 10. def:even n := C(2n, n), from 9
  exact ((Parley.Items.Stdlib.Divisibility.def_even (n := (LeanBridges.Counting.choose (2 * n) n : ℤ)))).mpr ⟨(LeanBridges.Counting.choose (2 * n - 1) (n - 1) : ℤ), s9⟩

end Parley.Proofs.Hammack.CentralBinomialEven.CentralBinomialEven
