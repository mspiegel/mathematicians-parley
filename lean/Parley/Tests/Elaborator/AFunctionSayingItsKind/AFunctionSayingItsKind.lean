module

public import Divisibility
public import SubstTactics
public import Tactics
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
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Rat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Ring.RingNF
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Sums

/-! Written from tests/elaborator/a-function-saying-its-kind.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AFunctionSayingItsKind.AFunctionSayingItsKind

theorem a_function_saying_its_kind (n : ℤ) (hH1 : 0 < n) :
    (∀ k : ℤ, k ∈ Finset.Icc 1 n → (∃ m : ℤ, (m : ℝ) = LeanBridges.Divisibility.mod ((k : ℝ) ^ (n - 1)) (n : ℝ) ∧ m ∈ Finset.Icc (0 : ℤ) (n - 1))) := by
  -- 1. mun:nat-minus-one
  have s1 : 0 ≤ n - 1 := by exact (Parley.Items.Stdlib.Numbers.mun_nat_minus_one (n := n) (by parley_side))
  have hD1_kind : ∀ k : ℤ, k ∈ Finset.Icc 1 n → (∃ m : ℤ, (m : ℝ) = LeanBridges.Divisibility.mod ((k : ℝ) ^ (n - 1)) (n : ℝ)) := by intro k h_k; exact (by
    have whole1 : ((k : ℝ) : ℝ) ^ (n - 1).toNat = (k : ℝ) ^ (n - 1) := by rw [← zpow_natCast, Int.toNat_of_nonneg s1]
    exact ⟨((k ^ (n - 1).toNat) % n), by (rw [← LeanBridges.Divisibility.mod_intCast _ _ (by omega)]; (push_cast; simp only [whole1]; all_goals ring))⟩)
  obtain ⟨f, hD1⟩ : ∃ g : ℤ → ℤ, ∀ k : ℤ, k ∈ Finset.Icc 1 n → (g k : ℝ) = LeanBridges.Divisibility.mod ((k : ℝ) ^ (n - 1)) (n : ℝ) := ⟨fun k => if h : k ∈ Finset.Icc 1 n then (hD1_kind k h).choose else 0, fun k h => by simp only [h, ↓reduceDIte]; exact (hD1_kind k h).choose_spec⟩
  -- 2. proof
  intro k hK1
  try push_cast at hK1
  try have hK1_bounds := Finset.mem_Icc.mp hK1
  -- 2.1. mun:power-integer m := n − 1, from 1
  have s2_1 : ∃ m : ℤ, (m : ℚ) = (k : ℚ) ^ (n - 1) := by
    have whole1 : ((k : ℚ) : ℚ) ^ (n - 1).toNat = (k : ℚ) ^ (n - 1) := by rw [← zpow_natCast, Int.toNat_of_nonneg s1]
    exact ⟨(k ^ (n - 1).toNat), by (push_cast; simp only [whole1]; all_goals ring)⟩
  -- 2.2. mun:mod-less, from 2.1
  have s2_2 : LeanBridges.Divisibility.mod ((k : ℝ) ^ (n - 1)) (n : ℝ) < (n : ℝ) := by rw [← (by have h := congrArg (fun x => ((x : ℚ) : ℝ)) (Classical.choose_spec s2_1); push_cast at h; exact h : ((Classical.choose s2_1 : ℤ) : ℝ) = (k : ℝ) ^ (n - 1))]; (try rw [LeanBridges.Divisibility.mod_intCast _ _ (by omega)]); (first | linarith [(Parley.Items.Stdlib.Divisibility.mun_mod_less (a := (Classical.choose s2_1)) (b := n) (by parley_side))] | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_less (a := (Classical.choose s2_1)) (b := n) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_mod_less (a := (Classical.choose s2_1)) (b := n) (by parley_side)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_less (a := (Classical.choose s2_1)) (b := n) (by parley_side)); parley_side))
  -- 2.3. mun:range-from-bounds, from 2.2
  have r29_1 : ∃ m : ℤ, 0 ≤ m ∧ (m : ℝ) = LeanBridges.Divisibility.mod ((k : ℝ) ^ (n - 1)) (n : ℝ) := by
    have whole1 : ∃ m : ℤ, (m : ℝ) = (k : ℝ) ^ (n - 1) := by obtain ⟨m, hm⟩ := s2_1; exact ⟨m, by have h := congrArg (fun x => ((x : ℚ) : ℝ)) hm; push_cast at h; exact h⟩
    refine ⟨((Classical.choose whole1 : ℤ) % n), ?_, by (rw [← LeanBridges.Divisibility.mod_intCast _ _ (by omega)]; (push_cast; simp only [Classical.choose_spec whole1]; all_goals ring))⟩
    (exact (Parley.Items.Stdlib.Divisibility.mun_mod_natural (a := (Classical.choose whole1 : ℤ)) (b := n) (by parley_side)))
  have s2_3 : ∃ m : ℤ, (m : ℝ) = LeanBridges.Divisibility.mod ((k : ℝ) ^ (n - 1)) (n : ℝ) ∧ m ∈ Finset.Icc (0 : ℤ) (n - 1) := by rw [← (Classical.choose_spec r29_1).2]; (try rw [LeanBridges.Divisibility.mod_intCast _ _ (by omega)]); have := (Classical.choose_spec r29_1).1; (try rw [← (Classical.choose_spec r29_1).2] at s2_2; norm_cast at s2_2); (first | exact (Parley.Items.Stdlib.Sums.mun_range_from_bounds (m := n) (by parley_side) (x := (Classical.choose r29_1)) (by parley_side) (by parley_side)) | exact ((Parley.Items.Stdlib.Sums.mun_range_from_bounds (m := n) (by parley_side) (x := (Classical.choose r29_1)) (by parley_side) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Sums.mun_range_from_bounds (m := n) (by parley_side) (x := (Classical.choose r29_1)) (by parley_side) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_range_from_bounds (m := n) (by parley_side) (x := (Classical.choose r29_1)) (by parley_side) (by parley_side)) | exact ⟨_, rfl, (Parley.Items.Stdlib.Sums.mun_range_from_bounds (m := n) (by parley_side) (x := (Classical.choose r29_1)) (by parley_side) (by parley_side))⟩ | (have h := (Parley.Items.Stdlib.Sums.mun_range_from_bounds (m := n) (by parley_side) (x := (Classical.choose r29_1)) (by parley_side) (by parley_side)); parley_side))
  -- 2.4. D1, from K1
  have s2_4 : (f k : ℝ) = LeanBridges.Divisibility.mod ((k : ℝ) ^ (n - 1)) (n : ℝ) := by simp (disch := omega) only [hD1]
  -- 2.5. substitute f(k) = (k^(n − 1)) mod n (line 2.4) into line 2.3
  have s2_5 : f k ∈ Finset.Icc (0 : ℤ) (n - 1) := by parley_subst_at s2_4 s2_3
  -- 2.6. substitute f(k) = (k^(n − 1)) mod n (line 2.4) into line 2.5
  exact ⟨_, s2_4, s2_5⟩

end Parley.Tests.Elaborator.AFunctionSayingItsKind.AFunctionSayingItsKind
