module

public import Divisibility
public import Batteries.Classes.RatCast
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Rat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Set
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Sums

/-! Written from tests/elaborator/a-function-narrowed-by-a-line.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AFunctionNarrowedByALine.AFunctionNarrowedByALine

theorem a_function_narrowed_by_a_line (n : ℤ) (hH1 : 0 < n) :
    (∀ k : ℤ, k ∈ Finset.Icc 1 n → (∃ m : ℤ, (m : ℝ) = LeanBridges.Divisibility.mod ((k : ℝ) ^ (n - 1)) (n : ℝ) ∧ m ∈ Finset.Icc (0 : ℤ) (n - 1))) := by
  set f : ℤ → ℝ := fun k : ℤ => LeanBridges.Divisibility.mod ((k : ℝ) ^ (n - 1)) (n : ℝ) with hD1
  -- 1. mun:nat-minus-one
  have s1 : 0 ≤ n - 1 := by exact (Parley.Items.Stdlib.Numbers.mun_nat_minus_one (n := n) hH1)
  -- 2. proof
  have s2 : ∀ k : ℤ, k ∈ Finset.Icc 1 n → (∃ m : ℤ, 0 ≤ m ∧ (m : ℝ) = f k) := by
    intro k hK1
    have hK1_bounds := Finset.mem_Icc.mp hK1
    -- 2.1. mun:power-integer m := n − 1, from 1
    have s2_1 : ∃ m : ℤ, (m : ℚ) = (k : ℚ) ^ (n - 1) := by
      have whole1 : ((k : ℚ) : ℚ) ^ (n - 1).toNat = (k : ℚ) ^ (n - 1) := by rw [← zpow_natCast, Int.toNat_of_nonneg s1]
      exact ⟨(k ^ (n - 1).toNat), by (push_cast; simp only [whole1])⟩
    -- 2.2. mun:mod-natural, from 2.1
    have s2_2 : ∃ m : ℤ, 0 ≤ m ∧ (m : ℝ) = LeanBridges.Divisibility.mod ((k : ℝ) ^ (n - 1)) (n : ℝ) := by
      have whole1 : ∃ m : ℤ, (m : ℝ) = (k : ℝ) ^ (n - 1) := by obtain ⟨m, hm⟩ := s2_1; exact ⟨m, by have h := congrArg (fun x => ((x : ℚ) : ℝ)) hm; push_cast at h; exact h⟩
      refine ⟨((Classical.choose whole1 : ℤ) % n), ?_, by (rw [← LeanBridges.Divisibility.mod_intCast _ _ (by omega)]; (push_cast; simp only [Classical.choose_spec whole1]))⟩
      (exact (Parley.Items.Stdlib.Divisibility.mun_mod_natural (a := (Classical.choose whole1 : ℤ)) (b := n) hH1))
    -- 2.3. D1, from K1
    have s2_3 : f k = LeanBridges.Divisibility.mod ((k : ℝ) ^ (n - 1)) (n : ℝ) := by simp (disch := omega) only [hD1]
    -- 2.4. substitute f(k) = (k^(n − 1)) mod n (line 2.3) into line 2.2
    exact Eq.subst (motive := (fun t : ℝ => ∃ m : ℤ, 0 ≤ m ∧ (m : ℝ) = t)) s2_3.symm s2_2
  obtain ⟨f, s2_pos, s2_eq⟩ : ∃ f' : ℤ → ℤ, (∀ k : ℤ, k ∈ Finset.Icc 1 n → 0 ≤ f' k) ∧ (∀ k : ℤ, k ∈ Finset.Icc 1 n → (f' k : ℝ) = f k) := ⟨fun k => if h : k ∈ Finset.Icc 1 n then (s2 k h).choose else 0, fun k h => by simp only [h, ↓reduceDIte]; exact (s2 k h).choose_spec.1, fun k h => by simp only [h, ↓reduceDIte]; exact (s2 k h).choose_spec.2⟩
  have hD1_f : ∀ k : ℤ, k ∈ Finset.Icc 1 n → (f k : ℝ) = LeanBridges.Divisibility.mod ((k : ℝ) ^ (n - 1)) (n : ℝ) := fun k h => (s2_eq k h).trans (by simp only [hD1])
  -- 3. proof
  intro k hK2
  have hK2_bounds := Finset.mem_Icc.mp hK2
  -- 3.1. mun:power-integer m := n − 1, from 1
  have s3_1 : ∃ m : ℤ, (m : ℚ) = (k : ℚ) ^ (n - 1) := by
    have whole1 : ((k : ℚ) : ℚ) ^ (n - 1).toNat = (k : ℚ) ^ (n - 1) := by rw [← zpow_natCast, Int.toNat_of_nonneg s1]
    exact ⟨(k ^ (n - 1).toNat), by (push_cast; simp only [whole1])⟩
  -- 3.2. mun:mod-less, from 3.1
  have s3_2 : LeanBridges.Divisibility.mod ((k : ℝ) ^ (n - 1)) (n : ℝ) < (n : ℝ) := by rw [← (by have h := congrArg (fun x => ((x : ℚ) : ℝ)) (Classical.choose_spec s3_1); push_cast at h; exact h : ((Classical.choose s3_1 : ℤ) : ℝ) = (k : ℝ) ^ (n - 1))]; rw [LeanBridges.Divisibility.mod_intCast _ _ (by omega)]; (exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_mod_less (a := (Classical.choose s3_1)) (b := n) hH1))
  -- 3.3. D1, from K2
  have s3_3 : (f k : ℝ) = LeanBridges.Divisibility.mod ((k : ℝ) ^ (n - 1)) (n : ℝ) := by simp (disch := omega) only [hD1_f]
  -- 3.4. substitute f(k) = (k^(n − 1)) mod n (line 3.3) into line 3.2
  have s3_4 : f k < n := by (have h := Eq.subst (motive := (fun t : ℝ => t < (n : ℝ))) s3_3.symm s3_2; push_cast at h ⊢; exact_mod_cast h)
  -- 3.5. mun:range-from-bounds, from 3.4
  have r50_1 : 0 ≤ f k := by exact (s2_pos k hK2)
  have s3_5 : f k ∈ Finset.Icc (0 : ℤ) (n - 1) := by exact (Parley.Items.Stdlib.Sums.mun_range_from_bounds (m := n) hH1 (x := f k) r50_1 s3_4)
  -- 3.6. substitute f(k) = (k^(n − 1)) mod n (line 3.3) into line 3.5
  exact ⟨_, s3_3, s3_5⟩

end Parley.Tests.Elaborator.AFunctionNarrowedByALine.AFunctionNarrowedByALine
