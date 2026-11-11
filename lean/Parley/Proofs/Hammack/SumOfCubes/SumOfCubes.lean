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
public import Mathlib.Tactic.Set
public import Parley.Items.Stdlib.Sums

/-! Written from proofs/hammack/sum-of-cubes.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.SumOfCubes.SumOfCubes

theorem sum_of_cubes (n : ℤ) (hH1 : 0 < n) :
    (∑ k ∈ Finset.Icc (1 : ℤ) n, ((k : ℚ) ^ 3 : ℚ)) = (n : ℚ) ^ 2 * ((n : ℚ) + 1) ^ 2 / 4 := by
  set S : ℤ → ℤ := fun m : ℤ => ∑ j ∈ Finset.Icc (1 : ℤ) m, (j ^ 3 : ℤ) with hD1
  -- 1. induction on k starting at 1
  have s1 : ∀ k : ℤ, 0 < k → (S k : ℚ) = (k : ℚ) ^ 2 * ((k : ℚ) + 1) ^ 2 / 4 := by
    intro k h_k
    replace h_k : 1 ≤ k := by omega
    induction k, h_k using LeanBridges.Functions.le_induction with
    | base =>
      -- 1.1. calculation
      have s1_1 : (S 1 : ℚ) = 1 ^ 2 * (1 + 1) ^ 2 / 4 := by
        calc (S 1 : ℚ) = (∑ j ∈ Finset.Icc (1 : ℤ) (1 : ℤ), ((j : ℚ) ^ 3 : ℚ)) := by simp (disch := omega) only [hD1]; push_cast; norm_num
          _ = 1 ^ 3 := by
              have hI : (∑ k ∈ Finset.Icc (1 : ℤ) (1 : ℤ), ((k : ℚ) ^ 3 : ℚ)) = 1 ^ 3 := by parley_instance ((Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (j : ℚ) ^ 3)) (a := (1 : ℤ))))
              exact hI
          _ = 1 ^ 2 * (1 + 1) ^ 2 / 4 := by norm_num
      (have h := s1_1; push_cast at h ⊢; all_goals exact h)
    | succ k hK hIH =>
      -- 1.2. calculation
      have r27_1 : k ≥ 1 := by parley_side
      have s1_2 : S (k + 1) = S k + (k + 1) ^ 3 := by
        calc S (k + 1) = (∑ j ∈ Finset.Icc (1 : ℤ) (k + 1), (j ^ 3 : ℤ)) := by simp (disch := omega) only [hD1]
          _ = (∑ j ∈ Finset.Icc (1 : ℤ) k, (j ^ 3 : ℤ)) + (k + 1) ^ 3 := by exact (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => j ^ 3)) (a := (1 : ℤ)) (n := k) r27_1)
          _ = S k + (k + 1) ^ 3 := by simp (disch := omega) only [hD1]
      -- 1.3. calculation
      have s1_3 : (S (k + 1) : ℚ) = ((k : ℚ) + 1) ^ 2 * ((k : ℚ) + 1 + 1) ^ 2 / 4 := by
        calc (S (k + 1) : ℚ) = (S k : ℚ) + ((k : ℚ) + 1) ^ 3 := by parley_side
          _ = (k : ℚ) ^ 2 * ((k : ℚ) + 1) ^ 2 / 4 + ((k : ℚ) + 1) ^ 3 := by (have h := congrArg (fun t : ℚ => t + ((k : ℚ) + 1) ^ 3) hIH; push_cast at h ⊢; all_goals exact_mod_cast h)
          _ = ((k : ℚ) + 1) ^ 2 * ((k : ℚ) + 1 + 1) ^ 2 / 4 := by parley_ring
      (have h := s1_3; push_cast at h ⊢; all_goals exact h)
  -- 2. calculation
  calc (∑ k ∈ Finset.Icc (1 : ℤ) n, ((k : ℚ) ^ 3 : ℚ)) = (S n : ℚ) := by simp (disch := omega) only [hD1]; push_cast; norm_num
    _ = (n : ℚ) ^ 2 * ((n : ℚ) + 1) ^ 2 / 4 := by exact (s1 n hH1)

end Parley.Proofs.Hammack.SumOfCubes.SumOfCubes
