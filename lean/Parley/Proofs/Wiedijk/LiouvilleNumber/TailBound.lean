module

public import AlgebraTactics
public import ArithTactics
public import Counting
public import FactorialTactics
public import Functions
public import NormTactics
public import OrderTactics
public import PowerTactics
public import SubstTactics
public import Tactics
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Rat.Defs
public import Mathlib.Data.Rat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.BigOperators
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Tactic.Set
public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Sums
public import Parley.Proofs.Wiedijk.LiouvilleNumber.FactorialGap
public import Parley.Proofs.Wiedijk.LiouvilleNumber.PartialSumReal
public import Parley.Proofs.Wiedijk.LiouvilleNumber.TermsReal

/-! Written from proofs/wiedijk/liouville-number.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.LiouvilleNumber.TailBound

set_option maxHeartbeats 600000 in
theorem tail_bound (n : ℤ) (hH1 : 0 < n) :
    (∀ j : ℤ, 0 ≤ j → (∑ k ∈ Finset.Icc (1 : ℤ) (n + j), (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) - (∑ k ∈ Finset.Icc (1 : ℤ) n, (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) ≤ 2 / 2 ^ LeanBridges.Counting.factorial (n + 1) - 2 / 2 ^ ((LeanBridges.Counting.factorial (n + 1) : ℤ) + j).toNat) := by
  have hD1_kind : 0 < (LeanBridges.Counting.factorial (n + 1) : ℤ) := by exact (Parley.Items.Stdlib.Counting.mun_factorial_nat (n := n + 1) (by parley_side))
  set A : ℤ := (LeanBridges.Counting.factorial (n + 1) : ℤ) with hD1
  have hD1_pos := hD1_kind
  -- 1. thm:factorial-gap
  have s1 : ∀ j : ℤ, 0 ≤ j → (LeanBridges.Counting.factorial (n + 1) : ℤ) + j ≤ (LeanBridges.Counting.factorial (n + 1 + j) : ℤ) := by exact (Parley.Proofs.Wiedijk.LiouvilleNumber.FactorialGap.factorial_gap (n := n) (by parley_side))
  -- 2. thm:partial-sum-real m := n
  -- 3. induction on j starting at 0
  have s3 : ∀ j : ℤ, 0 ≤ j → (∑ k ∈ Finset.Icc (1 : ℤ) (n + j), (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) - (∑ k ∈ Finset.Icc (1 : ℤ) n, (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) ≤ 2 / 2 ^ A.toNat - 2 / 2 ^ (A + j).toNat := by
    intro j h_j
    replace h_j : 0 ≤ j := by omega
    induction j, h_j using LeanBridges.Functions.le_induction with
    | base =>
      -- 3.1. algebra, from 2
      have s3_1 : (∑ k ∈ Finset.Icc (1 : ℤ) n, (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) - (∑ k ∈ Finset.Icc (1 : ℤ) n, (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) = 2 / 2 ^ A.toNat - 2 / 2 ^ A.toNat := by parley_ring
      -- 3.2. inequalities
      have s3_2 : (∑ k ∈ Finset.Icc (1 : ℤ) n, (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) - (∑ k ∈ Finset.Icc (1 : ℤ) n, (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) ≤ 2 / 2 ^ A.toNat - 2 / 2 ^ A.toNat := by parley_order
      simpa only [add_zero] using s3_2
    | succ j hK hIH =>
      -- 3.3. mun:nat-plus-nat0 a := n, b := j
      have s3_3 : 0 < n + j := by exact (Parley.Items.Stdlib.Numbers.mun_nat_plus_nat0 (a := n) (by parley_side) (b := j) (by parley_side))
      -- 3.4. mun:nat-plus-nat0 a := n + j, b := 1, from 3.3
      have s3_4 : 0 < n + j + 1 := (Parley.Items.Stdlib.Numbers.mun_nat_plus_nat0 (a := n + j) (by parley_side) (b := (1 : ℤ)) (by parley_side))
      -- 3.5. mun:power-positive a := 2, m := (n + j + 1)!
      have r142_1 : (2 : ℤ) > 0 := by parley_arith
      have s3_5 : (2 ^ LeanBridges.Counting.factorial (n + j + 1) : ℤ) > 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_power_positive (a := (2 : ℚ)) (m := (LeanBridges.Counting.factorial (n + j + 1) : ℤ)) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_power_positive (a := (2 : ℚ)) (m := (LeanBridges.Counting.factorial (n + j + 1) : ℤ)) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_power_positive (a := (2 : ℚ)) (m := (LeanBridges.Counting.factorial (n + j + 1) : ℤ)) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_power_positive (a := (2 : ℚ)) (m := (LeanBridges.Counting.factorial (n + j + 1) : ℤ)) (by parley_side)); parley_side)
      -- 3.6. algebra
      have s3_6 : n + j + 1 = n + (j + 1) := by parley_ring
      -- 3.7. substitute n + j + 1 = n + (j + 1) (line 3.6)
      have s3_7 : (∑ k ∈ Finset.Icc (1 : ℤ) (n + (j + 1)), (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) = (∑ k ∈ Finset.Icc (1 : ℤ) (n + j + 1), (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) := by
        have s3_6_w : (n : ℚ) + (j : ℚ) + 1 = (n : ℚ) + ((j : ℚ) + 1) := by have h := congrArg (fun x : ℤ => (x : ℚ)) s3_6; push_cast at h; linear_combination (norm := parley_norm) h
        first | parley_subst s3_6_w | parley_subst s3_6
      -- 3.8. thm:terms-real m := n + j + 1, from 3.4
      -- 3.9. mun:sum-extended a := 1, n := n + j, from 3.8
      have r155_1 : n + j ≥ 1 := by parley_order
      have s3_9 : (∑ k ∈ Finset.Icc (1 : ℤ) (n + j + 1), (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) = (∑ k ∈ Finset.Icc (1 : ℤ) (n + j), (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) + 1 / 2 ^ LeanBridges.Counting.factorial (n + j + 1) := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun k : ℤ => (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ))) (a := (1 : ℤ)) (n := n + j) r155_1)
      -- 3.10. algebra, from D0, 3.9
      have s3_10 : (∑ k ∈ Finset.Icc (1 : ℤ) (n + j + 1), (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) = (∑ k ∈ Finset.Icc (1 : ℤ) (n + j), (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) + 1 / 2 ^ LeanBridges.Counting.factorial (n + j + 1) := by linear_combination (norm := parley_field) s3_9
      -- 3.11. instantiate j := j in line 1, from D1
      have s3_11 : A + j ≤ (LeanBridges.Counting.factorial (n + 1 + j) : ℤ) := by first | linarith [(s1 j (by parley_side))] | (have h := (s1 j (by parley_side)); push_cast at h; linarith) | exact_mod_cast (s1 j (by parley_side)) | (have h := (s1 j (by parley_side)); parley_side)
      -- 3.12. substitute
      have s3_12 : A + j ≤ (LeanBridges.Counting.factorial (n + j + 1) : ℤ) := by
        have c1 : n + 1 + j = n + j + 1 := by parley_ring
        have row1 : A + j ≤ (LeanBridges.Counting.factorial (n + j + 1) : ℤ) := by parley_subst_at c1 s3_11
        exact row1
      -- 3.13. mun:power-exponent-le a := 2, m := A + j, n := (n + j + 1)!, from 3.12
      have r170_1 : (1 : ℤ) ≤ 2 := by parley_arith
      have s3_13 : (2 ^ (A + j).toNat : ℤ) ≤ 2 ^ LeanBridges.Counting.factorial (n + j + 1) := by first | (have h := (Parley.Items.Stdlib.Numbers.mun_power_exponent_le (a := (2 : ℤ)) (m := A + j) (by parley_side) (n := (LeanBridges.Counting.factorial (n + j + 1) : ℤ)) (by parley_side) (by parley_side) s3_12); simp (disch := first | omega | positivity | nlinarith) only [parley_zpow_toNat] at h ⊢; first | exact_mod_cast h | linarith) | linarith [(Parley.Items.Stdlib.Numbers.mun_power_exponent_le (a := (2 : ℤ)) (m := A + j) (by parley_side) (n := (LeanBridges.Counting.factorial (n + j + 1) : ℤ)) (by parley_side) (by parley_side) s3_12)] | (have h := (Parley.Items.Stdlib.Numbers.mun_power_exponent_le (a := (2 : ℤ)) (m := A + j) (by parley_side) (n := (LeanBridges.Counting.factorial (n + j + 1) : ℤ)) (by parley_side) (by parley_side) s3_12); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_power_exponent_le (a := (2 : ℤ)) (m := A + j) (by parley_side) (n := (LeanBridges.Counting.factorial (n + j + 1) : ℤ)) (by parley_side) (by parley_side) s3_12) | (have h := (Parley.Items.Stdlib.Numbers.mun_power_exponent_le (a := (2 : ℤ)) (m := A + j) (by parley_side) (n := (LeanBridges.Counting.factorial (n + j + 1) : ℤ)) (by parley_side) (by parley_side) s3_12); parley_side)
      -- 3.14. mun:power-positive a := 2, m := A + j
      have r174_1 : (2 : ℤ) > 0 := by parley_arith
      have s3_14 : (2 ^ (A + j).toNat : ℤ) > 0 := by first | (have h := (Parley.Items.Stdlib.Numbers.mun_power_positive (a := (2 : ℚ)) (m := A + j) (by parley_side)); simp (disch := first | omega | positivity | nlinarith) only [parley_zpow_toNat] at h ⊢; first | exact_mod_cast h | linarith) | linarith [(Parley.Items.Stdlib.Numbers.mun_power_positive (a := (2 : ℚ)) (m := A + j) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_power_positive (a := (2 : ℚ)) (m := A + j) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_power_positive (a := (2 : ℚ)) (m := A + j) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_power_positive (a := (2 : ℚ)) (m := A + j) (by parley_side)); parley_side)
      -- 3.15. mun:reciprocal-order x := 2^(A + j), y := 2^((n + j + 1)!), from 3.5, 3.13, 3.14
      have s3_15 : (1 / 2 ^ LeanBridges.Counting.factorial (n + j + 1) : ℚ) ≤ 1 / 2 ^ (A + j).toNat := ((Parley.Items.Stdlib.Numbers.mun_reciprocal_order (x := (2 ^ (A + j).toNat : ℚ)) (by parley_side) (y := (2 ^ LeanBridges.Counting.factorial (n + j + 1) : ℚ)) (by parley_side))).mp (by parley_side)
      -- 3.16. algebra
      have s3_16 : A + j + 1 = A + (j + 1) := by parley_ring
      -- 3.17. calculation
      have s3_17 : (2 ^ (A + j).toNat * 2 : ℤ) = 2 ^ (A + (j + 1)).toNat := by
        calc (2 ^ (A + j).toNat * 2 : ℤ) = 2 ^ (A + j + 1).toNat := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := A + j) (by parley_side)).symm
          _ = 2 ^ (A + (j + 1)).toNat := by parley_subst s3_16
      -- 3.18. algebra
      have s3_18 : (2 / (2 ^ (A + j).toNat * 2) : ℚ) = 1 / 2 ^ (A + j).toNat := by parley_ring
      -- 3.19. substitute 2^(A + j)·2 = 2^(A + (j + 1)) (line 3.17) into line 3.18
      have s3_19 : (2 / 2 ^ (A + (j + 1)).toNat : ℚ) = 1 / 2 ^ (A + j).toNat := by
        have s3_17_w : (2 ^ (A + j).toNat * 2 : ℚ) = 2 ^ (A + (j + 1)).toNat := by have h := congrArg (fun x : ℤ => (x : ℚ)) s3_17; push_cast at h; linear_combination (norm := parley_norm) h
        first | parley_subst_at s3_17_w s3_18 | parley_subst_at s3_17 s3_18 | (have e_nat : 2 ^ (A + j).toNat * 2 = 2 ^ (A + (j + 1)).toNat := by exact_mod_cast s3_17; parley_subst_at e_nat s3_18)
      -- 3.20. inequalities, from IH, 3.15
      have s3_20 : (∑ k ∈ Finset.Icc (1 : ℤ) (n + j), (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) - (∑ k ∈ Finset.Icc (1 : ℤ) n, (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) + 1 / 2 ^ LeanBridges.Counting.factorial (n + j + 1) ≤ 2 / 2 ^ A.toNat - 2 / 2 ^ (A + j).toNat + 1 / 2 ^ (A + j).toNat := by parley_order
      -- 3.21. calculation
      calc (∑ k ∈ Finset.Icc (1 : ℤ) (n + (j + 1)), (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) - (∑ k ∈ Finset.Icc (1 : ℤ) n, (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) = (∑ k ∈ Finset.Icc (1 : ℤ) (n + j), (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) - (∑ k ∈ Finset.Icc (1 : ℤ) n, (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) + 1 / 2 ^ LeanBridges.Counting.factorial (n + j + 1) := by linear_combination (norm := parley_field) s3_7 + s3_10
        _ ≤ 2 / 2 ^ A.toNat - 2 / 2 ^ (A + j).toNat + 1 / 2 ^ (A + j).toNat := by parley_side
        _ = 2 / 2 ^ A.toNat - 2 / 2 ^ (A + (j + 1)).toNat := by linear_combination (norm := parley_field) s3_19
  -- 4. substitute A = (n + 1)! (D1) into line 3
  intro j h_j
  have hD1_w : (A : ℚ) = (LeanBridges.Counting.factorial (n + 1) : ℚ) := by have h := congrArg (fun x : ℤ => (x : ℚ)) hD1; push_cast at h; linear_combination (norm := parley_norm) h
  first | parley_subst_at hD1_w s3 | parley_subst_at hD1 s3

end Parley.Proofs.Wiedijk.LiouvilleNumber.TailBound
