module

public import ArithTactics
public import SubstTactics
public import Tactics
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.BigOperators
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Positivity.Finset
public import Parley.Items.Stdlib.Sums

/-! Written from tests/notations/sums.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Sums.OneToThreeSummed

set_option maxHeartbeats 400000 in
theorem one_to_three_summed :
    (∑ k ∈ Finset.Icc (1 : ℤ) (3 : ℤ), (k : ℤ)) = 6 := by
  -- 1. mun:sum-single a := 1
  have s1 : (∑ k ∈ Finset.Icc (1 : ℤ) (1 : ℤ), (k : ℤ)) = 1 := by exact (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun k : ℤ => k)) (a := (1 : ℤ)))
  -- 2. mun:sum-extended a := 1, n := 1
  have r26_1 : (1 : ℤ) ≥ 1 := by parley_arith
  have s2 : (∑ k ∈ Finset.Icc (1 : ℤ) (1 + 1 : ℤ), (k : ℤ)) = (∑ k ∈ Finset.Icc (1 : ℤ) (1 : ℤ), (k : ℤ)) + (1 + 1) := by exact (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun k : ℤ => k)) (a := (1 : ℤ)) (n := (1 : ℤ)) r26_1)
  -- 3. mun:sum-extended a := 1, n := 2
  have r30_1 : (2 : ℤ) ≥ 1 := by parley_arith
  have s3 : (∑ k ∈ Finset.Icc (1 : ℤ) (2 + 1 : ℤ), (k : ℤ)) = (∑ k ∈ Finset.Icc (1 : ℤ) (2 : ℤ), (k : ℤ)) + (2 + 1) := by exact (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun k : ℤ => k)) (a := (1 : ℤ)) (n := (2 : ℤ)) r30_1)
  -- 4. arithmetic
  have s4 : (1 + 1 : ℤ) = 2 := by parley_arith
  -- 5. substitute 1 + 1 = 2 (line 4) into line 2
  have s5 : (∑ k ∈ Finset.Icc (1 : ℤ) (2 : ℤ), (k : ℤ)) = (∑ k ∈ Finset.Icc (1 : ℤ) (1 : ℤ), (k : ℤ)) + 2 := by first | parley_subst_at s4 s2 | (have e_nat : 1 + 1 = 2 := by exact_mod_cast s4; parley_subst_at e_nat s2)
  -- 6. substitute Σ(k = 1 to 1) k = 1 (line 1) into line 5
  have s6 : (∑ k ∈ Finset.Icc (1 : ℤ) (2 : ℤ), (k : ℤ)) = 1 + 2 := by (have h := Eq.subst (motive := (fun t : ℤ => (∑ k ∈ Finset.Icc (1 : ℤ) (2 : ℤ), (k : ℤ)) = t + 2)) s1 s5; push_cast at h ⊢; all_goals exact_mod_cast h)
  -- 7. calculation
  have s7 : (∑ k ∈ Finset.Icc (1 : ℤ) (2 : ℤ), (k : ℤ)) = 3 := by
    calc (∑ k ∈ Finset.Icc (1 : ℤ) (2 : ℤ), (k : ℤ)) = 1 + 2 := by exact s6
      _ = 3 := by norm_num
  -- 8. arithmetic
  have s8 : (2 + 1 : ℤ) = 3 := by parley_arith
  -- 9. substitute 2 + 1 = 3 (line 8) into line 3
  have s9 : (∑ k ∈ Finset.Icc (1 : ℤ) (3 : ℤ), (k : ℤ)) = (∑ k ∈ Finset.Icc (1 : ℤ) (2 : ℤ), (k : ℤ)) + 3 := by first | parley_subst_at s8 s3 | (have e_nat : 2 + 1 = 3 := by exact_mod_cast s8; parley_subst_at e_nat s3)
  -- 10. substitute Σ(k = 1 to 2) k = 3 (line 7) into line 9
  have s10 : (∑ k ∈ Finset.Icc (1 : ℤ) (3 : ℤ), (k : ℤ)) = 3 + 3 := by (have h := Eq.subst (motive := (fun t : ℤ => (∑ k ∈ Finset.Icc (1 : ℤ) (3 : ℤ), (k : ℤ)) = t + 3)) s7 s9; push_cast at h ⊢; all_goals exact_mod_cast h)
  -- 11. calculation
  calc (∑ k ∈ Finset.Icc (1 : ℤ) (3 : ℤ), (k : ℤ)) = 3 + 3 := by exact s10
    _ = 6 := by norm_num

end Parley.Tests.Notations.Sums.OneToThreeSummed
