module

public import AlgebraTactics
public import Functions
public import InstanceTactics
public import OrderTactics
public import Tactics
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Algebra.Order.ZeroLEOne
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

/-! Written from proofs/hammack/inverse-squares-bounded.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.InverseSquaresBounded.InverseSquaresBounded

theorem inverse_squares_bounded (n : ℤ) (hH1 : 0 < n) :
    (∑ k ∈ Finset.Icc (1 : ℤ) n, (1 / (k : ℚ) ^ 2 : ℚ)) ≤ 2 - 1 / (n : ℚ) := by
  -- 1. proof
  -- what this block shows, Lean's types give
  -- 2. induction on k starting at 1
  have s2 : ∀ k : ℤ, 0 < k → (∑ j ∈ Finset.Icc (1 : ℤ) k, (1 / (j : ℚ) ^ 2 : ℚ)) ≤ 2 - 1 / (k : ℚ) := by
    intro k h_k
    replace h_k : 1 ≤ k := by omega
    induction k, h_k using LeanBridges.Functions.le_induction with
    | base =>
      -- 2.1. calculation
      have s2_1 : (∑ j ∈ Finset.Icc (1 : ℤ) (1 : ℤ), (1 / (j : ℚ) ^ 2 : ℚ)) ≤ 2 - 1 / 1 := by
        calc (∑ j ∈ Finset.Icc (1 : ℤ) (1 : ℤ), (1 / (j : ℚ) ^ 2 : ℚ)) = 1 / 1 ^ 2 := by
              have hI : (∑ k ∈ Finset.Icc (1 : ℤ) (1 : ℤ), (1 / (k : ℚ) ^ 2 : ℚ)) = 1 / 1 ^ 2 := by parley_instance ((Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => 1 / (j : ℚ) ^ 2)) (a := (1 : ℤ))))
              exact hI
          _ ≤ 2 - 1 / 1 := by norm_num
      (have h := s2_1; push_cast at h ⊢; all_goals exact h)
    | succ k hK hIH =>
      -- 2.2. mun:sum-extended a := 1, n := k, from 1
      have r35_1 : k ≥ 1 := by parley_side
      have s2_2 : (∑ j ∈ Finset.Icc (1 : ℤ) (k + 1), (1 / (j : ℚ) ^ 2 : ℚ)) = (∑ j ∈ Finset.Icc (1 : ℤ) k, (1 / (j : ℚ) ^ 2 : ℚ)) + 1 / ((k : ℚ) + 1) ^ 2 := by
        have hI : (∑ b ∈ Finset.Icc (1 : ℤ) (k + 1), (1 / (b : ℚ) ^ 2 : ℚ)) = (∑ b ∈ Finset.Icc (1 : ℤ) k, (1 / (b : ℚ) ^ 2 : ℚ)) + 1 / ((k : ℚ) + 1) ^ 2 := by parley_instance ((Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => 1 / (j : ℚ) ^ 2)) (a := (1 : ℤ)) (n := k) r35_1))
        exact hI
      -- 2.3. inequalities, from K
      have s2_3 : k + 1 > 0 := by linarith only [lt_of_lt_of_le zero_lt_one hK]
      -- 2.4. algebra
      have s2_4 : 1 / (k : ℚ) - 1 / ((k : ℚ) + 1) = 1 / ((k : ℚ) * ((k : ℚ) + 1)) := by parley_ring
      -- 2.5. mun:square-positive x := k + 1
      have r45_1 : k + 1 ≠ 0 := ne_of_gt (by linarith only [s2_3])
      have s2_5 : (k + 1) ^ 2 > 0 := by exact (Parley.Items.Stdlib.Numbers.mun_square_positive (x := k + 1) r45_1)
      -- 2.6. mun:product-nonneg x := k, y := k + 1
      have r49_1 : k ≥ 0 := by linarith only [lt_of_lt_of_le zero_lt_one hK]
      have r49_2 : k + 1 ≥ 0 := by linarith only [s2_3]
      have s2_6 : k * (k + 1) ≥ 0 := by exact (Parley.Items.Stdlib.Numbers.mun_product_nonneg (x := k) (y := k + 1) r49_1 r49_2)
      -- 2.7. mun:product-nonzero x := k, y := k + 1
      have r54_1 : k ≠ 0 := by exact (lt_of_lt_of_le zero_lt_one hK).ne'
      have r54_2 : k + 1 ≠ 0 := ne_of_gt (by linarith only [s2_3])
      have s2_7 : k * (k + 1) ≠ 0 := by exact (Parley.Items.Stdlib.Numbers.mun_product_nonzero (x := k) (y := k + 1) r54_1 r54_2)
      -- 2.8. inequalities, from 2.6, 2.7
      have s2_8 : k * (k + 1) > 0 := Or.elim (Ne.lt_or_gt s2_7) (fun h1 => by linarith only [s2_6, h1]) (fun h1 => by linarith only [s2_6, h1])
      -- 2.9. algebra
      have s2_9 : (k + 1) ^ 2 = k * (k + 1) + (k + 1) := by parley_ring
      -- 2.10. inequalities
      have s2_10 : k * (k + 1) < k * (k + 1) + (k + 1) := by linarith only [s2_3]
      -- 2.11. transitivity, from 2.10, 2.9
      have s2_11 : k * (k + 1) < (k + 1) ^ 2 := by parley_order
      -- 2.12. inequalities
      have s2_12 : k * (k + 1) ≤ (k + 1) ^ 2 := by linarith only [s2_11]
      -- 2.13. mun:reciprocal-order x := k·(k + 1), y := (k + 1)², from 2.5, 2.8, 2.12
      have s2_13 : 1 / ((k : ℚ) + 1) ^ 2 ≤ 1 / ((k : ℚ) * ((k : ℚ) + 1)) := by exact ((Parley.Items.Stdlib.Numbers.mun_reciprocal_order (x := (k : ℚ) * ((k : ℚ) + 1)) (by exact_mod_cast gt_iff_lt.mp s2_8) (y := ((k : ℚ) + 1) ^ 2) (by exact_mod_cast gt_iff_lt.mp s2_5))).mp (by parley_side)
      -- 2.14. transitivity, from 2.13, 2.4
      have s2_14 : 1 / ((k : ℚ) + 1) ^ 2 ≤ 1 / (k : ℚ) - 1 / ((k : ℚ) + 1) := by parley_order
      -- 2.15. inequalities
      have s2_15 : (∑ j ∈ Finset.Icc (1 : ℤ) k, (1 / (j : ℚ) ^ 2 : ℚ)) + 1 / ((k : ℚ) + 1) ^ 2 ≤ 2 - 1 / (k : ℚ) + 1 / ((k : ℚ) + 1) ^ 2 := by linarith only [hIH]
      -- 2.16. inequalities
      have s2_16 : 2 - 1 / (k : ℚ) + 1 / ((k : ℚ) + 1) ^ 2 ≤ 2 - 1 / ((k : ℚ) + 1) := by linarith only [s2_14]
      -- 2.17. transitivity, from 2.2, 2.15, 2.16
      have s2_17 : (∑ j ∈ Finset.Icc (1 : ℤ) (k + 1), (1 / (j : ℚ) ^ 2 : ℚ)) ≤ 2 - 1 / ((k : ℚ) + 1) := by parley_order
      (have h := s2_17; push_cast at h ⊢; all_goals exact h)
  -- 3. instantiate k := n in line 2
  exact (s2 n hH1)

end Parley.Proofs.Hammack.InverseSquaresBounded.InverseSquaresBounded
