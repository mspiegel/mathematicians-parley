module

public import AlgebraTactics
public import Functions
public import InstanceTactics
public import Tactics
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
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
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.BigOperators
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Set
public import Parley.Items.Stdlib.Sums
public import Parley.Proofs.Wiedijk.SumFormula.SumFormula

/-! Written from proofs/hammack/square-of-sum-equals-sum-of-cubes.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.SquareOfSumEqualsSumOfCubes.SquareOfSumEqualsSumOfCubes

theorem square_of_sum_equals_sum_of_cubes (n : ℤ) (hH1 : 0 < n) :
    (∑ k ∈ Finset.Icc (1 : ℤ) n, (k : ℤ)) ^ 2 = (∑ k ∈ Finset.Icc (1 : ℤ) n, (k ^ 3 : ℤ)) := by
  set C : ℤ → ℤ := fun m : ℤ => ∑ j ∈ Finset.Icc (1 : ℤ) m, (j ^ 3 : ℤ) with hD1
  -- 1. induction on k starting at 1
  have s1 : ∀ k : ℤ, 0 < k → (C k : ℚ) = ((k : ℚ) * ((k : ℚ) + 1) / 2) ^ 2 := by
    intro k h_k
    replace h_k : 1 ≤ k := by omega
    induction k, h_k using LeanBridges.Functions.le_induction with
    | base =>
      -- 1.1. calculation
      have s1_1 : (C 1 : ℚ) = (1 * (1 + 1) / 2) ^ 2 := by
        calc (C 1 : ℚ) = (∑ j ∈ Finset.Icc (1 : ℤ) (1 : ℤ), ((j : ℚ) ^ 3 : ℚ)) := by simp (disch := omega) only [hD1]; push_cast; norm_num
          _ = 1 ^ 3 := by
              have hI : (∑ k ∈ Finset.Icc (1 : ℤ) (1 : ℤ), ((k : ℚ) ^ 3 : ℚ)) = 1 ^ 3 := by parley_instance ((Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (j : ℚ) ^ 3)) (a := (1 : ℤ))))
              exact hI
          _ = (1 * (1 + 1) / 2) ^ 2 := by norm_num
      first | exact_mod_cast s1_1 | (have h := s1_1; push_cast at h ⊢; exact h) | simpa using s1_1
    | succ k hK hIH =>
      -- 1.2. calculation
      have r29_1 : k ≥ 1 := by parley_side
      have s1_2 : C (k + 1) = C k + (k + 1) ^ 3 := by
        calc C (k + 1) = (∑ j ∈ Finset.Icc (1 : ℤ) (k + 1), (j ^ 3 : ℤ)) := by simp (disch := omega) only [hD1]
          _ = (∑ j ∈ Finset.Icc (1 : ℤ) k, (j ^ 3 : ℤ)) + (k + 1) ^ 3 := by exact (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => j ^ 3)) (a := (1 : ℤ)) (n := k) r29_1)
          _ = C k + (k + 1) ^ 3 := by simp (disch := omega) only [hD1]
      -- 1.3. calculation
      have s1_3 : (C (k + 1) : ℚ) = (((k : ℚ) + 1) * ((k : ℚ) + 1 + 1) / 2) ^ 2 := by
        calc (C (k + 1) : ℚ) = (C k : ℚ) + ((k : ℚ) + 1) ^ 3 := by parley_side
          _ = ((k : ℚ) * ((k : ℚ) + 1) / 2) ^ 2 + ((k : ℚ) + 1) ^ 3 := by (have h := congrArg (fun t : ℚ => t + ((k : ℚ) + 1) ^ 3) hIH; push_cast at h ⊢; all_goals exact_mod_cast h)
          _ = (((k : ℚ) + 1) * ((k : ℚ) + 1 + 1) / 2) ^ 2 := by parley_ring
      first | exact_mod_cast s1_3 | (have h := s1_3; push_cast at h ⊢; exact h) | simpa using s1_3
  -- 2. thm:sum-formula
  have s2 : (∑ k ∈ Finset.Icc (1 : ℤ) n, ((k : ℚ) : ℚ)) = (n : ℚ) * ((n : ℚ) + 1) / 2 := by exact (Parley.Proofs.Wiedijk.SumFormula.SumFormula.sum_formula (n := n) (by parley_side))
  -- 3. calculation
  try qify
  calc (∑ k ∈ Finset.Icc (1 : ℤ) n, ((k : ℚ) : ℚ)) ^ 2 = ((n : ℚ) * ((n : ℚ) + 1) / 2) ^ 2 := by (have h := congrArg (fun t : ℚ => t ^ 2) s2; push_cast at h ⊢; all_goals exact_mod_cast h)
    _ = (C n : ℚ) := by exact ((s1 n (by parley_side))).symm
    _ = (∑ k ∈ Finset.Icc (1 : ℤ) n, ((k : ℚ) ^ 3 : ℚ)) := by simp (disch := omega) only [hD1]; push_cast; norm_num

end Parley.Proofs.Hammack.SquareOfSumEqualsSumOfCubes.SquareOfSumEqualsSumOfCubes
