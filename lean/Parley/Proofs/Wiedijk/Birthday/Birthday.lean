module

public import Functions
public import Batteries.Util.ExtendedBinder
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Rat.Defs
public import Mathlib.Data.Rat.Init
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Order.Basic
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.BigOperators
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Set
public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Sums

/-! Written from proofs/wiedijk/birthday.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.Birthday.Birthday

theorem birthday :
    ({a ∈ LeanBridges.Functions.functions_from (Set.Icc (1 : ℤ) (23 : ℤ) : Set ℤ) (Set.Icc (1 : ℤ) (365 : ℤ) : Set ℤ) | Set.MapsTo a Set.univ (Set.Icc (1 : ℤ) (365 : ℤ) : Set ℤ) ∧ Set.InjOn a Set.univ}.ncard : ℚ) / ((LeanBridges.Functions.functions_from (Set.Icc (1 : ℤ) (23 : ℤ) : Set ℤ) (Set.Icc (1 : ℤ) (365 : ℤ) : Set ℤ)).ncard : ℚ) < 1 / 2 := by
  set S : Set (↥((Set.Icc (1 : ℤ) (23 : ℤ) : Set ℤ)) → ℤ) := LeanBridges.Functions.functions_from (Set.Icc (1 : ℤ) (23 : ℤ) : Set ℤ) (Set.Icc (1 : ℤ) (365 : ℤ) : Set ℤ) with hD1
  have hD1_finite : S.Finite := by rw [hD1]; exact LeanBridges.Functions.functions_from_finite (Set.finite_Icc _ _) (Set.finite_Icc _ _)
  set T : Set (↥((Set.Icc (1 : ℤ) (23 : ℤ) : Set ℤ)) → ℤ) := {f ∈ S | Set.MapsTo f Set.univ (Set.Icc (1 : ℤ) (365 : ℤ) : Set ℤ) ∧ Set.InjOn f Set.univ} with hD2
  have hD2_finite : T.Finite := by rw [hD2]; exact (hD1_finite).subset (fun _ h => h.1)
  -- 1. mun:range-finite a := 1, b := 23
  have s1 : (Set.Icc (1 : ℤ) (23 : ℤ) : Set ℤ).Finite := by exact (Parley.Items.Stdlib.Sums.mun_range_finite (a := (1 : ℤ)) (b := (23 : ℤ)))
  -- 2. mun:range-finite a := 1, b := 365
  have s2 : (Set.Icc (1 : ℤ) (365 : ℤ) : Set ℤ).Finite := by exact (Parley.Items.Stdlib.Sums.mun_range_finite (a := (1 : ℤ)) (b := (365 : ℤ)))
  -- 3. mun:range-size n := 23
  have s3 : ((Set.Icc (1 : ℤ) (23 : ℤ) : Set ℤ).ncard : ℤ) = 23 := by exact (Parley.Items.Stdlib.Counting.mun_range_size (n := (23 : ℤ)) (by norm_num))
  -- 4. mun:range-size n := 365
  have s4 : ((Set.Icc (1 : ℤ) (365 : ℤ) : Set ℤ).ncard : ℤ) = 365 := by exact (Parley.Items.Stdlib.Counting.mun_range_size (n := (365 : ℤ)) (by norm_num))
  -- 5. thm:count-functions X := {1, …, 23}, Y := {1, …, 365}, from D1, 1, 2
  have s5 : (S.ncard : ℤ) = ((Set.Icc (1 : ℤ) (365 : ℤ) : Set ℤ).ncard : ℤ) ^ (Set.Icc (1 : ℤ) (23 : ℤ) : Set ℤ).ncard := by
    simp only [hD1] at ⊢
    push_cast at ⊢
    (have h := (Parley.Items.Stdlib.Counting.thm_count_functions (X := (Set.Icc (1 : ℤ) (23 : ℤ) : Set ℤ)) (Y := (Set.Icc (1 : ℤ) (365 : ℤ) : Set ℤ)) s1 s2); push_cast at h; exact h)
  -- 6. substitute
  have s6 : (S.ncard : ℤ) = 365 ^ 23 := by
    have c1 : ((Set.Icc (1 : ℤ) (365 : ℤ) : Set ℤ).ncard : ℤ) = 365 := by
      have e_nat : (Set.Icc (1 : ℤ) (365 : ℤ) : Set ℤ).ncard = 365 := by exact_mod_cast s4
      have e_w : ((Set.Icc (1 : ℤ) (365 : ℤ) : Set ℤ).ncard : ℤ) = 365 := by have h := congrArg (fun x : ℕ => (x : ℤ)) e_nat; push_cast at h ⊢; linear_combination h
      exact congrArg (fun t : ℤ => t) e_w
    have row1 : (S.ncard : ℤ) = 365 ^ (Set.Icc (1 : ℤ) (23 : ℤ) : Set ℤ).ncard := by
      have e_nat : (Set.Icc (1 : ℤ) (365 : ℤ) : Set ℤ).ncard = 365 := by exact_mod_cast c1
      have e_w : ((Set.Icc (1 : ℤ) (365 : ℤ) : Set ℤ).ncard : ℤ) = 365 := by have h := congrArg (fun x : ℕ => (x : ℤ)) e_nat; push_cast at h ⊢; linear_combination h
      exact Eq.subst (motive := (fun t : ℤ => (S.ncard : ℤ) = t ^ (Set.Icc (1 : ℤ) (23 : ℤ) : Set ℤ).ncard)) e_w s5
    have c2 : ((Set.Icc (1 : ℤ) (23 : ℤ) : Set ℤ).ncard : ℤ) = 23 := by
      have e_nat : (Set.Icc (1 : ℤ) (23 : ℤ) : Set ℤ).ncard = 23 := by exact_mod_cast s3
      have e_w : ((Set.Icc (1 : ℤ) (23 : ℤ) : Set ℤ).ncard : ℤ) = 23 := by have h := congrArg (fun x : ℕ => (x : ℤ)) e_nat; push_cast at h ⊢; linear_combination h
      exact congrArg (fun t : ℤ => t) e_w
    have row2 : (S.ncard : ℤ) = 365 ^ 23 := by
      have e_nat : (Set.Icc (1 : ℤ) (23 : ℤ) : Set ℤ).ncard = 23 := by exact_mod_cast c2
      exact Eq.subst (motive := (fun t : ℕ => (S.ncard : ℤ) = 365 ^ t)) e_nat row1
    exact row2
  -- 7. arithmetic
  have s7 : (23 : ℤ) ≤ 365 := by norm_num
  -- 8. transitivity, from 3, 7, 4
  have s8 : ((Set.Icc (1 : ℤ) (23 : ℤ) : Set ℤ).ncard : ℤ) ≤ ((Set.Icc (1 : ℤ) (365 : ℤ) : Set ℤ).ncard : ℤ) := by exact LE.le.trans_eq (Eq.trans_le s3 s7) s4.symm
  -- 9. thm:count-one-to-one X := {1, …, 23}, Y := {1, …, 365}, from D1, D2, 1, 2, 8
  have s9 : (T.ncard : ℤ) = (∏ k ∈ Finset.Icc (0 : ℤ) (((Set.Icc (1 : ℤ) (23 : ℤ) : Set ℤ).ncard : ℤ) - 1), (((Set.Icc (1 : ℤ) (365 : ℤ) : Set ℤ).ncard : ℤ) - k : ℤ)) := by
    simp only [hD1, hD2] at ⊢
    push_cast at ⊢
    (have h := (Parley.Items.Stdlib.Counting.thm_count_one_to_one (X := (Set.Icc (1 : ℤ) (23 : ℤ) : Set ℤ)) (Y := (Set.Icc (1 : ℤ) (365 : ℤ) : Set ℤ)) s1 s2 s8); push_cast at h; exact h)
  -- 10. substitute
  have s10 : (T.ncard : ℤ) = (∏ k ∈ Finset.Icc (0 : ℤ) (22 : ℤ), (365 - k : ℤ)) := by
    have c1 : ((Set.Icc (1 : ℤ) (23 : ℤ) : Set ℤ).ncard : ℤ) = 23 := by
      have e_nat : (Set.Icc (1 : ℤ) (23 : ℤ) : Set ℤ).ncard = 23 := by exact_mod_cast s3
      have e_w : ((Set.Icc (1 : ℤ) (23 : ℤ) : Set ℤ).ncard : ℤ) = 23 := by have h := congrArg (fun x : ℕ => (x : ℤ)) e_nat; push_cast at h ⊢; linear_combination h
      exact congrArg (fun t : ℤ => t) e_w
    have row1 : (T.ncard : ℤ) = (∏ k ∈ Finset.Icc (0 : ℤ) (23 - 1 : ℤ), (((Set.Icc (1 : ℤ) (365 : ℤ) : Set ℤ).ncard : ℤ) - k : ℤ)) := by
      have e_nat : (Set.Icc (1 : ℤ) (23 : ℤ) : Set ℤ).ncard = 23 := by exact_mod_cast c1
      (have h := Eq.subst (motive := (fun t : ℕ => (T.ncard : ℤ) = (∏ k ∈ Finset.Icc (0 : ℤ) ((t : ℤ) - 1), (((Set.Icc (1 : ℤ) (365 : ℤ) : Set ℤ).ncard : ℤ) - k : ℤ)))) e_nat s9; push_cast at h ⊢; exact_mod_cast h)
    have c2 : (23 - 1 : ℤ) = 22 := by norm_num
    have row2 : (T.ncard : ℤ) = (∏ k ∈ Finset.Icc (0 : ℤ) (22 : ℤ), (((Set.Icc (1 : ℤ) (365 : ℤ) : Set ℤ).ncard : ℤ) - k : ℤ)) := by (have h := Eq.subst (motive := (fun t : ℤ => (T.ncard : ℤ) = (∏ k ∈ Finset.Icc (0 : ℤ) t, (((Set.Icc (1 : ℤ) (365 : ℤ) : Set ℤ).ncard : ℤ) - k : ℤ)))) c2 row1; push_cast at h ⊢; exact_mod_cast h)
    have c3 : ((Set.Icc (1 : ℤ) (365 : ℤ) : Set ℤ).ncard : ℤ) = 365 := by
      have e_nat : (Set.Icc (1 : ℤ) (365 : ℤ) : Set ℤ).ncard = 365 := by exact_mod_cast s4
      have e_w : ((Set.Icc (1 : ℤ) (365 : ℤ) : Set ℤ).ncard : ℤ) = 365 := by have h := congrArg (fun x : ℕ => (x : ℤ)) e_nat; push_cast at h ⊢; linear_combination h
      exact congrArg (fun t : ℤ => t) e_w
    have row3 : (T.ncard : ℤ) = (∏ k ∈ Finset.Icc (0 : ℤ) (22 : ℤ), (365 - k : ℤ)) := by
      have e_nat : (Set.Icc (1 : ℤ) (365 : ℤ) : Set ℤ).ncard = 365 := by exact_mod_cast c3
      (have h := Eq.subst (motive := (fun t : ℕ => (T.ncard : ℤ) = (∏ k ∈ Finset.Icc (0 : ℤ) (22 : ℤ), ((t : ℤ) - k : ℤ)))) e_nat row2; push_cast at h ⊢; exact_mod_cast h)
    exact row3
  -- 11. arithmetic
  have s11 : (∏ k ∈ Finset.Icc (0 : ℤ) (22 : ℤ), (365 - (k : ℚ) : ℚ)) / 365 ^ 23 < 1 / 2 := by field_simp; norm_cast
  -- 12. calculation
  calc (T.ncard : ℚ) / (S.ncard : ℚ) = (T.ncard : ℚ) / 365 ^ 23 := by
        have e_nat : S.ncard = 365 ^ 23 := by exact_mod_cast s6
        have e_w : (S.ncard : ℚ) = 365 ^ 23 := by have h := congrArg (fun x : ℕ => (x : ℚ)) e_nat; push_cast at h ⊢; linear_combination h
        exact congrArg (fun t : ℚ => (T.ncard : ℚ) / t) e_w
    _ = (∏ k ∈ Finset.Icc (0 : ℤ) (22 : ℤ), (365 - (k : ℚ) : ℚ)) / 365 ^ 23 := by
        have e_w : (T.ncard : ℚ) = (∏ k ∈ Finset.Icc (0 : ℤ) (22 : ℤ), (365 - (k : ℚ) : ℚ)) := by have h := congrArg (fun x : ℤ => (x : ℚ)) s10; push_cast at h ⊢; linear_combination h
        exact congrArg (fun t : ℚ => t / 365 ^ 23) e_w
    _ < 1 / 2 := s11

end Parley.Proofs.Wiedijk.Birthday.Birthday
