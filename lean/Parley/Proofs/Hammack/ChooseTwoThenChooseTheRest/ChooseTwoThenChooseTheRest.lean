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
public import Parley.Items.Stdlib.Sums

/-! Written from proofs/hammack/choose-two-then-choose-the-rest.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.ChooseTwoThenChooseTheRest.ChooseTwoThenChooseTheRest

set_option maxHeartbeats 400000 in
theorem choose_two_then_choose_the_rest (n : ℤ) (hH1 : 0 < n) (k : ℤ) (hH2 : 0 < k) (hH3 : 2 ≤ k) (hH4 : k ≤ n) :
    (LeanBridges.Counting.choose n (2 : ℤ) : ℤ) * (LeanBridges.Counting.choose (n - 2) (k - 2) : ℤ) = (LeanBridges.Counting.choose n k : ℤ) * (LeanBridges.Counting.choose k (2 : ℤ) : ℤ) := by
  -- 1. transitivity, from H3, H4
  have s1 : 2 ≤ n := by parley_order
  -- 2. inequalities, from 1
  have s2a : (0 : ℤ) ≤ 2 := by parley_order
  have s2b : 2 ≤ n := by parley_order
  -- 3. inequalities, from H3
  have s3a : (0 : ℤ) ≤ 2 := by parley_order
  have s3b : 2 ≤ k := by parley_order
  -- 4. inequalities, from H2, H4
  have s4a : 0 ≤ k := by parley_order
  have s4b : k ≤ n := by parley_order
  -- 5. inequalities
  have s5 : 0 ≤ k - 2 := by parley_order
  -- 6. inequalities
  have s6 : k - 2 ≤ n - 2 := by parley_order
  -- 7. def:range-between k := 2, a := 0, b := n, from 2
  have s7 : (2 : ℤ) ∈ Finset.Icc (0 : ℤ) n := ((Parley.Items.Stdlib.Sums.def_range_between (k := (2 : ℤ)) (a := (0 : ℤ)) (b := n))).mpr (by parley_side)
  -- 8. def:range-between k := 2, a := 0, b := k, from 3
  have s8 : (2 : ℤ) ∈ Finset.Icc (0 : ℤ) k := ((Parley.Items.Stdlib.Sums.def_range_between (k := (2 : ℤ)) (a := (0 : ℤ)) (b := k))).mpr (by parley_side)
  -- 9. def:range-between a := 0, b := n, from 4
  have s9 : k ∈ Finset.Icc (0 : ℤ) n := ((Parley.Items.Stdlib.Sums.def_range_between (k := k) (a := (0 : ℤ)) (b := n))).mpr (by parley_side)
  -- 10. def:range-between k := k − 2, a := 0, b := n − 2, from 5, 6
  have s10 : k - 2 ∈ Finset.Icc (0 : ℤ) (n - 2) := ((Parley.Items.Stdlib.Sums.def_range_between (k := k - 2) (a := (0 : ℤ)) (b := n - 2))).mpr (by parley_side)
  -- 11. mun:range-difference a := 0, k := 2, from 7
  have s11 : 0 ≤ n - 2 := by exact (Parley.Items.Stdlib.Sums.mun_range_difference (a := (0 : ℤ)) (n := n) (k := (2 : ℤ)) s7)
  -- 12. mun:range-difference a := 0, n := k, k := 2, from 8
  have s12 : 0 ≤ k - 2 := by exact (Parley.Items.Stdlib.Sums.mun_range_difference (a := (0 : ℤ)) (n := k) (k := (2 : ℤ)) s8)
  -- 13. mun:range-difference a := 0, from 9
  have s13 : 0 ≤ n - k := by exact (Parley.Items.Stdlib.Sums.mun_range_difference (a := (0 : ℤ)) (n := n) (k := k) s9)
  -- 14. def:C k := 2, from 7
  have s14 : (LeanBridges.Counting.choose n (2 : ℤ) : ℚ) = (LeanBridges.Counting.factorial n : ℚ) / ((LeanBridges.Counting.factorial (n - 2) : ℚ) * (LeanBridges.Counting.factorial (2 : ℤ) : ℚ)) := by exact (Parley.Items.Stdlib.Counting.def_C_2 (n := n) (by parley_side) (k := (2 : ℤ))) s7
  -- 15. def:C n := n − 2, k := k − 2, from 10, 11
  have s15 : (LeanBridges.Counting.choose (n - 2) (k - 2) : ℚ) = (LeanBridges.Counting.factorial (n - 2) : ℚ) / ((LeanBridges.Counting.factorial (n - 2 - (k - 2)) : ℚ) * (LeanBridges.Counting.factorial (k - 2) : ℚ)) := by exact (Parley.Items.Stdlib.Counting.def_C_2 (n := n - 2) (by parley_side) (k := k - 2)) s10
  -- 16. def:C, from 9
  have s16 : (LeanBridges.Counting.choose n k : ℚ) = (LeanBridges.Counting.factorial n : ℚ) / ((LeanBridges.Counting.factorial (n - k) : ℚ) * (LeanBridges.Counting.factorial k : ℚ)) := by exact (Parley.Items.Stdlib.Counting.def_C_2 (n := n) (by parley_side) (k := k)) s9
  -- 17. def:C n := k, k := 2, from 8
  have s17 : (LeanBridges.Counting.choose k (2 : ℤ) : ℚ) = (LeanBridges.Counting.factorial k : ℚ) / ((LeanBridges.Counting.factorial (k - 2) : ℚ) * (LeanBridges.Counting.factorial (2 : ℤ) : ℚ)) := by exact (Parley.Items.Stdlib.Counting.def_C_2 (n := k) (by parley_side) (k := (2 : ℤ))) s8
  -- 18. algebra
  have s18 : n - 2 - (k - 2) = n - k := by parley_ring
  -- 19. substitute
  have s19 : (LeanBridges.Counting.choose (n - 2) (k - 2) : ℚ) = (LeanBridges.Counting.factorial (n - 2) : ℚ) / ((LeanBridges.Counting.factorial (n - k) : ℚ) * (LeanBridges.Counting.factorial (k - 2) : ℚ)) := by
    have c1 : n - 2 - (k - 2) = n - k := by parley_subst s18
    have c1_w : (n : ℚ) - 2 - ((k : ℚ) - 2) = (n : ℚ) - (k : ℚ) := by have h := congrArg (fun x : ℤ => (x : ℚ)) c1; push_cast at h; linear_combination (norm := parley_norm) h
    have row1 : (LeanBridges.Counting.choose (n - 2) (k - 2) : ℚ) = (LeanBridges.Counting.factorial (n - 2) : ℚ) / ((LeanBridges.Counting.factorial (n - k) : ℚ) * (LeanBridges.Counting.factorial (k - 2) : ℚ)) := by first | parley_put_at c1_w s15 | parley_put_at c1 s15 | parley_subst_at c1_w s15 | parley_subst_at c1 s15
    exact row1
  -- 20. calculation
  have r78_1 : 0 < (LeanBridges.Counting.factorial (n - 2) : ℤ) := by exact (Parley.Items.Stdlib.Counting.mun_factorial_nat (n := n - 2) (by parley_side))
  have r78_2 : 0 < (LeanBridges.Counting.factorial (n - k) : ℤ) := by exact (Parley.Items.Stdlib.Counting.mun_factorial_nat (n := n - k) (by parley_side))
  have r78_3 : 0 < (LeanBridges.Counting.factorial (k - 2) : ℤ) := by exact (Parley.Items.Stdlib.Counting.mun_factorial_nat (n := k - 2) (by parley_side))
  try qify
  calc (LeanBridges.Counting.choose n (2 : ℤ) : ℚ) * (LeanBridges.Counting.choose (n - 2) (k - 2) : ℚ) = (LeanBridges.Counting.factorial n : ℚ) / ((LeanBridges.Counting.factorial (n - 2) : ℚ) * (LeanBridges.Counting.factorial (2 : ℤ) : ℚ)) * (LeanBridges.Counting.choose (n - 2) (k - 2) : ℚ) := by parley_subst s14
    _ = (LeanBridges.Counting.factorial n : ℚ) / ((LeanBridges.Counting.factorial (n - 2) : ℚ) * (LeanBridges.Counting.factorial (2 : ℤ) : ℚ)) * ((LeanBridges.Counting.factorial (n - 2) : ℚ) / ((LeanBridges.Counting.factorial (n - k) : ℚ) * (LeanBridges.Counting.factorial (k - 2) : ℚ))) := by parley_subst s19
    _ = (LeanBridges.Counting.factorial n : ℚ) / ((LeanBridges.Counting.factorial (n - k) : ℚ) * (LeanBridges.Counting.factorial k : ℚ)) * ((LeanBridges.Counting.factorial k : ℚ) / ((LeanBridges.Counting.factorial (k - 2) : ℚ) * (LeanBridges.Counting.factorial (2 : ℤ) : ℚ))) := by parley_ring
    _ = (LeanBridges.Counting.factorial n : ℚ) / ((LeanBridges.Counting.factorial (n - k) : ℚ) * (LeanBridges.Counting.factorial k : ℚ)) * (LeanBridges.Counting.choose k (2 : ℤ) : ℚ) := by parley_subst s17
    _ = (LeanBridges.Counting.choose n k : ℚ) * (LeanBridges.Counting.choose k (2 : ℤ) : ℚ) := by parley_subst s16

end Parley.Proofs.Hammack.ChooseTwoThenChooseTheRest.ChooseTwoThenChooseTheRest
