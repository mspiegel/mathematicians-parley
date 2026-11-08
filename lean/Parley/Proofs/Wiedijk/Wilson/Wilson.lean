module

public import AlgebraTactics
public import ArithTactics
public import Counting
public import Divisibility
public import FactorialTactics
public import NormTactics
public import OrderTactics
public import PowerTactics
public import SetTactics
public import SubstTactics
public import Tactics
public import WholeTactics
public import Batteries.Classes.RatCast
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.BigOperators
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.SetNotationForOrder
public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Functions
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Reasoning
public import Parley.Items.Stdlib.Sets
public import Parley.Items.Stdlib.Sums
public import Parley.Proofs.Wiedijk.DivisibilityByThree.CongruentTimes
public import Parley.Proofs.Wiedijk.Euler.Euler
public import Parley.Proofs.Wiedijk.Wilson.CoprimeBelowPrime
public import Parley.Proofs.Wiedijk.Wilson.PairedProduct

/-! Written from proofs/wiedijk/wilson.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.Wilson.Wilson

set_option maxHeartbeats 2200000 in
theorem wilson (p : ℤ) (hH1 : 0 < p) (hH2 : Nat.Prime p.toNat) :
    (LeanBridges.Counting.factorial (p - 1) : ℤ) ≡ (-1 : ℤ) [ZMOD p] := by
  -- 1. def:prime, from H2
  have s1 : p > 1 := (((Parley.Items.Stdlib.Divisibility.def_prime (p := p) (by parley_set_side))).mp hH2).1
  -- 2. mun:integer-step m := 1, n := p, from 1
  have s2 : 1 + 1 ≤ p := (Parley.Items.Stdlib.Numbers.mun_integer_step (m := (1 : ℤ)) (n := p) s1)
  -- 3. substitute 1 + 1 = 2 (arithmetic) into line 2
  have s3 : 2 ≤ p := by parley_subst_at (show (1 + 1 : ℤ) = 2 by parley_set_side) s2
  -- 4. mun:le-cases x := 2, y := p, from 3
  have s4 : 2 < p ∨ 2 = p := ((Parley.Items.Stdlib.Numbers.mun_le_cases (x := (2 : ℤ)) (y := p))).mp s3
  -- 5. cases, from 4
  rcases s4 with hC1 | hC2
  · skip
    -- 5.1. mun:integer-step m := 2, n := p, from C1
    have s5_1 : 2 + 1 ≤ p := (Parley.Items.Stdlib.Numbers.mun_integer_step (m := (2 : ℤ)) (n := p) hC1)
    -- 5.2. substitute 2 + 1 = 3 (arithmetic) into line 5.1
    have s5_2 : 3 ≤ p := by parley_subst_at (show (2 + 1 : ℤ) = 3 by parley_set_side) s5_1
    -- 5.3. mun:pos-int-nat m := p − 2
    have r321_1 : 0 < p - 2 := by parley_order
    have s5_3 : 0 < p - 2 := by exact (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := p - 2) r321_1)
    have hD1_kind : ∀ a : ℤ, a ∈ Finset.Icc 2 (p - 2) → (∃ m : ℤ, (m : ℝ) = LeanBridges.Divisibility.mod ((a : ℝ) ^ (p - 2)) (p : ℝ)) := by intro a h_a; exact (by
      have whole1 : ((a : ℝ) : ℝ) ^ (p - 2).toNat = (a : ℝ) ^ (p - 2) := by rw [← zpow_natCast, Int.toNat_of_nonneg (le_of_lt s5_3)]
      exact ⟨((a ^ (p - 2).toNat) % p), by first | (rw [← LeanBridges.Divisibility.mod_intCast _ _ (by omega)]; (push_cast; simp only [whole1]; done)) | (rw [← LeanBridges.Divisibility.mod_intCast _ _ (by omega)]; (push_cast; simp only [whole1]; ring))⟩)
    obtain ⟨f, hD1⟩ : ∃ g : ℤ → ℤ, ∀ a : ℤ, a ∈ Finset.Icc 2 (p - 2) → (g a : ℝ) = LeanBridges.Divisibility.mod ((a : ℝ) ^ (p - 2)) (p : ℝ) := ⟨fun a => if h : a ∈ Finset.Icc 2 (p - 2) then (hD1_kind a h).choose else 0, fun a h => by simp only [h, ↓reduceDIte]; exact (hD1_kind a h).choose_spec⟩
    -- 5.4. proof
    have s5_4 : ∀ a : ℤ, a ∈ Finset.Icc 2 (p - 2) → (Int.gcd a p : ℤ) = 1 := by
      intro a hK1
      try push_cast at hK1
      try have hK1_bounds := Finset.mem_Icc.mp hK1
      -- 5.4.1. mun:pos-int-nat m := a
      have r333_1 : 0 < a := by parley_order
      have s5_4_1 : 0 < a := by exact (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := a) r333_1)
      -- 5.4.2. thm:coprime-below-prime, from H2, 5.4.1
      have r337_1 : a < p := by parley_order
      exact (Parley.Proofs.Wiedijk.Wilson.CoprimeBelowPrime.coprime_below_prime (p := p) (by parley_set_side) hH2 (a := a) (by parley_set_side) r337_1)
    -- 5.5. proof
    have s5_5 : ∀ a : ℤ, a ∈ Finset.Icc 2 (p - 2) → f a ∈ Finset.Icc (0 : ℤ) (p - 1) := by
      intro a hK2
      try push_cast at hK2
      try have hK2_bounds := Finset.mem_Icc.mp hK2
      -- 5.5.1. mun:power-integer m := p − 2, from 5.3
      have s5_5_1 : ∃ m : ℤ, (m : ℚ) = (a : ℚ) ^ (p - 2) := by
        have whole1 : ((a : ℚ) : ℚ) ^ (p - 2).toNat = (a : ℚ) ^ (p - 2) := by rw [← zpow_natCast, Int.toNat_of_nonneg (le_of_lt s5_3)]
        exact ⟨(a ^ (p - 2).toNat), by first | (push_cast; simp only [whole1]; done) | (push_cast; simp only [whole1]; ring)⟩
      -- 5.5.2. mun:mod-less, from 5.5.1
      have s5_5_2 : LeanBridges.Divisibility.mod ((a : ℝ) ^ (p - 2)) (p : ℝ) < (p : ℝ) := by rw [← (by first | exact_mod_cast Classical.choose_spec s5_5_1 | (have h := congrArg (fun x => ((x : ℚ) : ℝ)) (Classical.choose_spec s5_5_1); push_cast at h; exact h) : ((Classical.choose s5_5_1 : ℤ) : ℝ) = (a : ℝ) ^ (p - 2))]; (try rw [LeanBridges.Divisibility.mod_intCast _ _ (by omega)]); (first | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_less (a := (Classical.choose s5_5_1)) (b := p) (by parley_set_side)); simp (disch := first | omega | positivity | nlinarith) only [parley_zpow_toNat] at h ⊢; first | exact_mod_cast h | linarith) | linarith [(Parley.Items.Stdlib.Divisibility.mun_mod_less (a := (Classical.choose s5_5_1)) (b := p) (by parley_set_side))] | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_less (a := (Classical.choose s5_5_1)) (b := p) (by parley_set_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_mod_less (a := (Classical.choose s5_5_1)) (b := p) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_less (a := (Classical.choose s5_5_1)) (b := p) (by parley_set_side)); parley_set_side))
      -- 5.5.3. mun:range-from-bounds, from 5.5.2
      have r351_1 : ∃ m : ℤ, 0 ≤ m ∧ (m : ℝ) = LeanBridges.Divisibility.mod ((a : ℝ) ^ (p - 2)) (p : ℝ) := by
        have whole1 : ∃ m : ℤ, (m : ℝ) = (a : ℝ) ^ (p - 2) := by obtain ⟨m, hm⟩ := s5_5_1; exact ⟨m, by first | exact_mod_cast hm | (have h := congrArg (fun x => ((x : ℚ) : ℝ)) hm; push_cast at h; exact h)⟩
        refine ⟨((Classical.choose whole1 : ℤ) % p), ?_, by first | (rw [← LeanBridges.Divisibility.mod_intCast _ _ (by omega)]; (push_cast; simp only [Classical.choose_spec whole1]; done)) | (rw [← LeanBridges.Divisibility.mod_intCast _ _ (by omega)]; (push_cast; simp only [Classical.choose_spec whole1]; ring))⟩
        (exact (Parley.Items.Stdlib.Divisibility.mun_mod_natural (a := (Classical.choose whole1 : ℤ)) (b := p) (by parley_set_side)))
      have s5_5_3 : ∃ m : ℤ, (m : ℝ) = LeanBridges.Divisibility.mod ((a : ℝ) ^ (p - 2)) (p : ℝ) ∧ m ∈ Finset.Icc (0 : ℤ) (p - 1) := by rw [← (Classical.choose_spec r351_1).2]; (try rw [LeanBridges.Divisibility.mod_intCast _ _ (by omega)]); have := (Classical.choose_spec r351_1).1; (try rw [← (Classical.choose_spec r351_1).2] at s5_5_2; norm_cast at s5_5_2); (first | exact (Parley.Items.Stdlib.Sums.mun_range_from_bounds (m := p) (by parley_set_side) (x := (Classical.choose r351_1)) (by parley_set_side) (by parley_set_side)) | exact ((Parley.Items.Stdlib.Sums.mun_range_from_bounds (m := p) (by parley_set_side) (x := (Classical.choose r351_1)) (by parley_set_side) (by parley_set_side))).symm | simpa using (Parley.Items.Stdlib.Sums.mun_range_from_bounds (m := p) (by parley_set_side) (x := (Classical.choose r351_1)) (by parley_set_side) (by parley_set_side)) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_range_from_bounds (m := p) (by parley_set_side) (x := (Classical.choose r351_1)) (by parley_set_side) (by parley_set_side)) | exact ⟨_, rfl, (Parley.Items.Stdlib.Sums.mun_range_from_bounds (m := p) (by parley_set_side) (x := (Classical.choose r351_1)) (by parley_set_side) (by parley_set_side))⟩ | (have h := (Parley.Items.Stdlib.Sums.mun_range_from_bounds (m := p) (by parley_set_side) (x := (Classical.choose r351_1)) (by parley_set_side) (by parley_set_side)); parley_set_side))
      -- 5.5.4. D1, from K2
      have s5_5_4 : (f a : ℝ) = LeanBridges.Divisibility.mod ((a : ℝ) ^ (p - 2)) (p : ℝ) := by simp (disch := omega) only [hD1]
      -- 5.5.5. substitute f(a) = (a^(p − 2)) mod p (line 5.5.4) into line 5.5.3
      parley_subst_at s5_5_4 s5_5_3
    -- 5.6. proof
    -- what this block shows, Lean's types give
    -- 5.7. proof
    have s5_7 : ∀ a : ℤ, a ∈ Finset.Icc 2 (p - 2) → a * f a ≡ (1 : ℤ) [ZMOD p] := by
      intro a hK4
      try push_cast at hK4
      try have hK4_bounds := Finset.mem_Icc.mp hK4
      -- 5.7.1. thm:euler n := p, from 5.4
      have s5_7_1 : a ^ Nat.totient p.toNat ≡ (1 : ℤ) [ZMOD p] := by exact (Parley.Proofs.Wiedijk.Euler.Euler.euler (n := p) (by parley_set_side) (a := a) (s5_4 a (by parley_set_side)))
      -- 5.7.2. substitute
      have r376_1 : 0 ≤ p - 1 := by exact (Parley.Items.Stdlib.Numbers.mun_nat_minus_one (n := p) (by parley_set_side))
      have s5_7_2 : ∃ m : ℤ, (m : ℚ) = (a : ℚ) ^ (p - 1) ∧ m ≡ (1 : ℤ) [ZMOD p] := by
        have whole1 : ((a : ℚ) : ℚ) ^ (p - 1).toNat = (a : ℚ) ^ (p - 1) := by rw [← zpow_natCast, Int.toNat_of_nonneg r376_1]
        refine ⟨(a ^ (p - 1).toNat), by first | (push_cast; simp only [whole1]; done) | (push_cast; simp only [whole1]; ring), ?_⟩
        exact (by
          have c1 : (Nat.totient p.toNat : ℤ) = p - 1 := by exact (Parley.Items.Stdlib.Divisibility.thm_phi_prime (p := p) (by parley_set_side) hH2)
          have row1 : (a ^ (p - 1).toNat) ≡ (1 : ℤ) [ZMOD p] := by parley_subst_at c1 s5_7_1
          exact row1)
      -- 5.7.3. mun:exponent-step m := p − 2, from 5.3
      have s5_7_3 : (a : ℚ) ^ (p - 2 + 1) = (a : ℚ) ^ (p - 2) * (a : ℚ) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (a : ℚ)) (m := p - 2) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (a : ℚ)) (m := p - 2) (by parley_set_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (a : ℚ)) (m := p - 2) (by parley_set_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (a : ℚ)) (m := p - 2) (by parley_set_side)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (a : ℚ)) (m := p - 2) (by parley_set_side))).symm | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (a : ℚ)) (m := p - 2) (by parley_set_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (a : ℚ)) (m := p - 2) (by parley_set_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (a : ℚ)) (m := p - 2) (by parley_set_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (a : ℚ)) (m := p - 2) (by parley_set_side)); parley_set_side)
      -- 5.7.4. substitute
      have s5_7_4 : (a : ℚ) ^ (p - 1) = (a : ℚ) ^ (p - 2) * (a : ℚ) := by
        have c1 : p - 2 + 1 = p - 1 := by parley_ring
        have c1_w : (p : ℚ) - 2 + 1 = (p : ℚ) - 1 := by have h := congrArg (fun x : ℤ => (x : ℚ)) c1; push_cast at h; linear_combination (norm := parley_norm) h
        have row1 : (a : ℚ) ^ (p - 1) = (a : ℚ) ^ (p - 2) * (a : ℚ) := by first | parley_put_at c1_w s5_7_3 | parley_put_at c1 s5_7_3 | parley_subst_at c1_w s5_7_3 | parley_subst_at c1 s5_7_3
        exact row1
      -- 5.7.5. mun:power-integer m := p − 2, from 5.3
      have s5_7_5 : ∃ m : ℤ, (m : ℚ) = (a : ℚ) ^ (p - 2) := by
        have whole1 : ((a : ℚ) : ℚ) ^ (p - 2).toNat = (a : ℚ) ^ (p - 2) := by rw [← zpow_natCast, Int.toNat_of_nonneg (le_of_lt s5_3)]
        exact ⟨(a ^ (p - 2).toNat), by first | (push_cast; simp only [whole1]; done) | (push_cast; simp only [whole1]; ring)⟩
      -- 5.7.6. mun:mod-congruent x := a^(p − 2), n := p, from 5.7.5
      have s5_7_6 : ∃ m : ℤ, (m : ℚ) = (a : ℚ) ^ (p - 2) ∧ m ≡ m % p [ZMOD p] := by
        have whole1 : ∃ m : ℤ, (m : ℚ) = (a : ℚ) ^ (p - 2) := by obtain ⟨m, hm⟩ := s5_7_5; exact ⟨m, by first | exact_mod_cast hm | (have h := congrArg (fun x => ((x : ℚ) : ℝ)) hm; push_cast at h; exact h)⟩
        (try rw [← (by first | exact_mod_cast Classical.choose_spec whole1 | (have h := congrArg (fun x => ((x : ℚ) : ℝ)) (Classical.choose_spec whole1); push_cast at h; exact h) : ((Classical.choose whole1 : ℤ) : ℝ) = (a : ℝ) ^ (p - 2))] at s5_7_5; (try rw [LeanBridges.Divisibility.mod_intCast _ _ (by omega)] at s5_7_5); norm_cast at s5_7_5)
        refine ⟨(Classical.choose whole1 : ℤ), by first | (push_cast; simp only [Classical.choose_spec whole1]; done) | (push_cast; simp only [Classical.choose_spec whole1]; ring), ?_⟩
        (exact (Parley.Items.Stdlib.Divisibility.mun_mod_congruent (x := (Classical.choose whole1 : ℤ)) (n := p) (by parley_set_side)))
      -- 5.7.7. D1, from K4
      have s5_7_7 : (f a : ℝ) = LeanBridges.Divisibility.mod ((a : ℝ) ^ (p - 2)) (p : ℝ) := by simp (disch := omega) only [hD1]
      -- 5.7.8. substitute f(a) = (a^(p − 2)) mod p (line 5.7.7) into line 5.7.6
      have r399_1 : ∃ m : ℤ, (m : ℚ) = (a : ℚ) ^ (p - 2) := by
        have whole1 : ∃ m : ℤ, (m : ℚ) = (a : ℚ) ^ (p - 2) := by obtain ⟨m, hm⟩ := s5_7_5; exact ⟨m, by first | exact_mod_cast hm | (have h := congrArg (fun x => ((x : ℚ) : ℝ)) hm; push_cast at h; exact h)⟩
        exact ⟨(Classical.choose whole1 : ℤ), by first | (push_cast; simp only [Classical.choose_spec whole1]; done) | (push_cast; simp only [Classical.choose_spec whole1]; ring)⟩
      have s5_7_8 : ∃ m : ℤ, (m : ℚ) = (a : ℚ) ^ (p - 2) ∧ m ≡ f a [ZMOD p] := by
        have whole1 : ∃ m : ℤ, (m : ℚ) = (a : ℚ) ^ (p - 2) := by obtain ⟨m, hm⟩ := r399_1; exact ⟨m, by first | exact_mod_cast hm | (have h := congrArg (fun x => ((x : ℚ) : ℝ)) hm; push_cast at h; exact h)⟩
        have s5_7_6 := parley_witness_at s5_7_6 (Classical.choose whole1 : ℤ) (by first | (push_cast; simp only [Classical.choose_spec whole1]; done) | (push_cast; simp only [Classical.choose_spec whole1]; ring))
        (try rw [← (by first | exact_mod_cast Classical.choose_spec whole1 | (have h := congrArg (fun x => ((x : ℚ) : ℝ)) (Classical.choose_spec whole1); push_cast at h; exact h) : ((Classical.choose whole1 : ℤ) : ℝ) = (a : ℝ) ^ (p - 2))] at s5_7_7; (try rw [LeanBridges.Divisibility.mod_intCast _ _ (by omega)] at s5_7_7); norm_cast at s5_7_7)
        refine ⟨(Classical.choose whole1 : ℤ), by first | (push_cast; simp only [Classical.choose_spec whole1]; done) | (push_cast; simp only [Classical.choose_spec whole1]; ring), ?_⟩
        (parley_subst_at s5_7_7 s5_7_6)
      -- 5.7.9. thm:congruent-times c := a, from 5.6, 5.7.5, 5.7.8
      have s5_7_9 : ∃ m : ℤ, (m : ℚ) = (a : ℚ) ^ (p - 2) * (a : ℚ) ∧ f a * a ≡ m [ZMOD p] := by
        have whole1 : ∃ m : ℤ, (m : ℚ) = (a : ℚ) ^ (p - 2) := by obtain ⟨m, hm⟩ := s5_7_5; exact ⟨m, by first | exact_mod_cast hm | (have h := congrArg (fun x => ((x : ℚ) : ℝ)) hm; push_cast at h; exact h)⟩
        have s5_7_8 := parley_witness_at s5_7_8 (Classical.choose whole1 : ℤ) (by first | (push_cast; simp only [Classical.choose_spec whole1]; done) | (push_cast; simp only [Classical.choose_spec whole1]; ring))
        (try rw [← (by first | exact_mod_cast Classical.choose_spec whole1 | (have h := congrArg (fun x => ((x : ℚ) : ℝ)) (Classical.choose_spec whole1); push_cast at h; exact h) : ((Classical.choose whole1 : ℤ) : ℝ) = (a : ℝ) ^ (p - 2))] at s5_7_5; (try rw [LeanBridges.Divisibility.mod_intCast _ _ (by omega)] at s5_7_5); norm_cast at s5_7_5)
        refine ⟨((Classical.choose whole1 : ℤ) * a), by first | (push_cast; simp only [Classical.choose_spec whole1]; done) | (push_cast; simp only [Classical.choose_spec whole1]; ring), ?_⟩
        (exact (Parley.Proofs.Wiedijk.DivisibilityByThree.CongruentTimes.congruent_times (a := f a) (b := (Classical.choose whole1 : ℤ)) (c := a) (n := p) (by parley_set_side) s5_7_8.symm))
      -- 5.7.10. substitute a^(p − 1) = a^(p − 2)·a (line 5.7.4) into line 5.7.9
      have r406_2 : ∃ m : ℤ, (m : ℚ) = (a : ℚ) ^ (p - 1) := by
        have other : ∃ m : ℤ, (m : ℚ) = (a : ℚ) ^ (p - 2) * (a : ℚ) := by
          have whole1 : ∃ m : ℤ, (m : ℚ) = (a : ℚ) ^ (p - 2) := by obtain ⟨m, hm⟩ := s5_7_5; exact ⟨m, by first | exact_mod_cast hm | (have h := congrArg (fun x => ((x : ℚ) : ℝ)) hm; push_cast at h; exact h)⟩
          exact ⟨((Classical.choose whole1 : ℤ) * a), by first | (push_cast; simp only [Classical.choose_spec whole1]; done) | (push_cast; simp only [Classical.choose_spec whole1]; ring)⟩
        rw [s5_7_4]
        exact other
      have s5_7_10 : ∃ m : ℤ, (m : ℚ) = (a : ℚ) ^ (p - 1) ∧ f a * a ≡ m [ZMOD p] := by
        have whole1 : ∃ m : ℤ, (m : ℚ) = (a : ℚ) ^ (p - 1) := by obtain ⟨m, hm⟩ := r406_2; exact ⟨m, by first | exact_mod_cast hm | (have h := congrArg (fun x => ((x : ℚ) : ℝ)) hm; push_cast at h; exact h)⟩
        (try rw [← (by first | exact_mod_cast Classical.choose_spec whole1 | (have h := congrArg (fun x => ((x : ℚ) : ℝ)) (Classical.choose_spec whole1); push_cast at h; exact h) : ((Classical.choose whole1 : ℤ) : ℝ) = (a : ℝ) ^ (p - 1))] at s5_7_4; (try rw [LeanBridges.Divisibility.mod_intCast _ _ (by omega)] at s5_7_4); norm_cast at s5_7_4)
        (try rw [← (by first | exact_mod_cast Classical.choose_spec whole1 | (have h := congrArg (fun x => ((x : ℚ) : ℝ)) (Classical.choose_spec whole1); push_cast at h; exact h) : ((Classical.choose whole1 : ℤ) : ℝ) = (a : ℝ) ^ (p - 1))] at s5_7_9; (try rw [LeanBridges.Divisibility.mod_intCast _ _ (by omega)] at s5_7_9); norm_cast at s5_7_9)
        refine ⟨(Classical.choose whole1 : ℤ), by first | (push_cast; simp only [Classical.choose_spec whole1]; done) | (push_cast; simp only [Classical.choose_spec whole1]; ring), ?_⟩
        (first | parley_subst_at s5_7_4 s5_7_9 | exact parley_witness_at s5_7_9 ((Classical.choose whole1 : ℤ)) (by push_cast; (try simp only [Classical.choose_spec whole1]); linear_combination (norm := parley_norm) s5_7_4) | exact parley_witness_at s5_7_9 ((Classical.choose whole1 : ℤ)) (by push_cast; (try simp only [Classical.choose_spec whole1]); linear_combination (norm := parley_norm) -s5_7_4))
      -- 5.7.11. algebra, from 5.6
      have s5_7_11 : a * f a = f a * a := by parley_ring
      -- 5.7.12. membership, from 5.7.4, 5.7.5
      have s5_7_12 : ∃ m : ℤ, (m : ℚ) = (a : ℚ) ^ (p - 1) := by
        have other : ∃ m : ℤ, (m : ℚ) = (a : ℚ) ^ (p - 2) * (a : ℚ) := by
          have whole1 : ∃ m : ℤ, (m : ℚ) = (a : ℚ) ^ (p - 2) := by obtain ⟨m, hm⟩ := s5_7_5; exact ⟨m, by first | exact_mod_cast hm | (have h := congrArg (fun x => ((x : ℚ) : ℝ)) hm; push_cast at h; exact h)⟩
          exact ⟨((Classical.choose whole1 : ℤ) * a), by first | (push_cast; simp only [Classical.choose_spec whole1]; done) | (push_cast; simp only [Classical.choose_spec whole1]; ring)⟩
        rw [s5_7_4]
        exact other
      -- 5.7.13. calculation
      have r417_2 : ∃ m : ℤ, (m : ℚ) = (a : ℚ) ^ (p - 1) := by
        have whole1 : ∃ m : ℤ, (m : ℚ) = (a : ℚ) ^ (p - 1) := by obtain ⟨m, hm⟩ := s5_7_12; exact ⟨m, by first | exact_mod_cast hm | (have h := congrArg (fun x => ((x : ℚ) : ℝ)) hm; push_cast at h; exact h)⟩
        exact ⟨(Classical.choose whole1 : ℤ), by first | (push_cast; simp only [Classical.choose_spec whole1]; done) | (push_cast; simp only [Classical.choose_spec whole1]; ring)⟩
      have whole1 : ∃ m : ℤ, (m : ℚ) = (a : ℚ) ^ (p - 1) := by obtain ⟨m, hm⟩ := r417_2; exact ⟨m, by first | exact_mod_cast hm | (have h := congrArg (fun x => ((x : ℚ) : ℝ)) hm; push_cast at h; exact h)⟩
      have s5_7_10 := parley_witness_at s5_7_10 (Classical.choose whole1 : ℤ) (by first | (push_cast; simp only [Classical.choose_spec whole1]; done) | (push_cast; simp only [Classical.choose_spec whole1]; ring))
      have s5_7_2 := parley_witness_at s5_7_2 (Classical.choose whole1 : ℤ) (by first | (push_cast; simp only [Classical.choose_spec whole1]; done) | (push_cast; simp only [Classical.choose_spec whole1]; ring))
      (try rw [← (by first | exact_mod_cast Classical.choose_spec whole1 | (have h := congrArg (fun x => ((x : ℚ) : ℝ)) (Classical.choose_spec whole1); push_cast at h; exact h) : ((Classical.choose whole1 : ℤ) : ℝ) = (a : ℝ) ^ (p - 1))] at s5_7_11; (try rw [LeanBridges.Divisibility.mod_intCast _ _ (by omega)] at s5_7_11); norm_cast at s5_7_11)
      calc a * f a = f a * a := by first | parley_set_side | (qify; push_cast; simp only [Classical.choose_spec whole1]; first | (linear_combination (norm := parley_norm) s5_7_11; done) | (linear_combination (norm := parley_norm) -s5_7_11; done))
        _ ≡ (Classical.choose whole1 : ℤ) [ZMOD p] := by first | parley_set_side | (qify; push_cast; simp only [Classical.choose_spec whole1]; first | (linear_combination (norm := parley_norm) s5_7_10; done) | (linear_combination (norm := parley_norm) -s5_7_10; done))
        _ ≡ 1 [ZMOD p] := by first | parley_set_side | (qify; push_cast; simp only [Classical.choose_spec whole1]; first | (linear_combination (norm := parley_norm) s5_7_2; done) | (linear_combination (norm := parley_norm) -s5_7_2; done))
    -- 5.8. proof
    have s5_8 : ∀ a : ℤ, a ∈ Finset.Icc 2 (p - 2) → ¬ p ∣ a - 1 := by
      intro a hK5
      try push_cast at hK5
      try have hK5_bounds := Finset.mem_Icc.mp hK5
      -- 5.8.1. mun:pos-int-nat m := a − 1
      have r429_1 : 0 < a - 1 := by parley_order
      have s5_8_1 : 0 < a - 1 := by exact (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := a - 1) r429_1)
      -- 5.8.2. mun:below-not-divisible n := p, x := a − 1, from 5.8.1
      have r433_1 : a - 1 < p := by parley_order
      exact (Parley.Items.Stdlib.Divisibility.mun_below_not_divisible (n := p) (by parley_set_side) (x := a - 1) (by parley_set_side) r433_1)
    -- 5.9. proof
    have s5_9 : ∀ a : ℤ, a ∈ Finset.Icc 2 (p - 2) → ¬ p ∣ a + 1 := by
      intro a hK6
      try push_cast at hK6
      try have hK6_bounds := Finset.mem_Icc.mp hK6
      -- 5.9.1. mun:pos-int-nat m := a + 1
      have r441_1 : 0 < a + 1 := by parley_order
      have s5_9_1 : 0 < a + 1 := by exact (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := a + 1) r441_1)
      -- 5.9.2. mun:below-not-divisible n := p, x := a + 1, from 5.9.1
      have r445_1 : a + 1 < p := by parley_order
      exact (Parley.Items.Stdlib.Divisibility.mun_below_not_divisible (n := p) (by parley_set_side) (x := a + 1) (by parley_set_side) r445_1)
    -- 5.10. mun:range-from-bounds m := p, x := 0, from H1
    have s5_10 : (0 : ℤ) ∈ Finset.Icc (0 : ℤ) (p - 1) := by exact (Parley.Items.Stdlib.Sums.mun_range_from_bounds (m := p) (by parley_set_side) (x := (0 : ℤ)) (by parley_set_side) hH1)
    -- 5.11. mun:range-from-bounds m := p, x := 1, from 1
    have s5_11 : (1 : ℤ) ∈ Finset.Icc (0 : ℤ) (p - 1) := by exact (Parley.Items.Stdlib.Sums.mun_range_from_bounds (m := p) (by parley_set_side) (x := (1 : ℤ)) (by parley_set_side) s1)
    -- 5.12. mun:range-inside
    have r455_1 : (0 : ℤ) ≤ 2 := by parley_arith
    have r455_2 : p - 2 ≤ p - 1 := by parley_order
    have s5_12 : (Set.Icc (2 : ℤ) (p - 2) : Set ℤ) ⊆ (Set.Icc (0 : ℤ) (p - 1) : Set ℤ) := by exact (Parley.Items.Stdlib.Sums.mun_range_inside (a := (2 : ℤ)) (b := p - 2) (c := (0 : ℤ)) (d := p - 1) r455_1 r455_2)
    -- 5.13. proof
    have s5_13 : ∀ a : ℤ, a ∈ Finset.Icc 2 (p - 2) → f a ∈ Finset.Icc (2 : ℤ) (p - 2) := by
      intro a hK7
      try push_cast at hK7
      try have hK7_bounds := Finset.mem_Icc.mp hK7
      -- 5.13.1. mun:in-subset, from K7, 5.12
      have s5_13_1 : a ∈ Finset.Icc (0 : ℤ) (p - 1) := by first | exact (Parley.Items.Stdlib.Sets.mun_in_subset (X := (Set.Icc (2 : ℤ) (p - 2) : Set ℤ)) (Y := (Set.Icc (0 : ℤ) (p - 1) : Set ℤ)) (u := a) (by parley_whole_side) (by parley_whole_side)) | exact ((Parley.Items.Stdlib.Sets.mun_in_subset (X := (Set.Icc (2 : ℤ) (p - 2) : Set ℤ)) (Y := (Set.Icc (0 : ℤ) (p - 1) : Set ℤ)) (u := a) (by parley_whole_side) (by parley_whole_side))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_in_subset (X := (Set.Icc (2 : ℤ) (p - 2) : Set ℤ)) (Y := (Set.Icc (0 : ℤ) (p - 1) : Set ℤ)) (u := a) (by parley_whole_side) (by parley_whole_side)) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_in_subset (X := (Set.Icc (2 : ℤ) (p - 2) : Set ℤ)) (Y := (Set.Icc (0 : ℤ) (p - 1) : Set ℤ)) (u := a) (by parley_whole_side) (by parley_whole_side)) | (have h := (Parley.Items.Stdlib.Sets.mun_in_subset (X := (Set.Icc (2 : ℤ) (p - 2) : Set ℤ)) (Y := (Set.Icc (0 : ℤ) (p - 1) : Set ℤ)) (u := a) (by parley_whole_side) (by parley_whole_side)); parley_set_side)
      -- 5.13.2. contradiction
      have s5_13_2 : f a ≠ 0 := by
        intro hS1
        -- 5.13.2.1. substitute f(a) = 0 (S1) into line 5.7
        have s5_13_2_1 : a * 0 ≡ (1 : ℤ) [ZMOD p] := by
          have at0 := (s5_7 a (by parley_set_side))
          parley_subst_at hS1 at0
        -- 5.13.2.2. substitute
        have s5_13_2_2 : (0 : ℤ) ≡ (1 : ℤ) [ZMOD p] := by
          have c1 : a * 0 = 0 := by parley_ring
          have row1 : (0 : ℤ) ≡ (1 : ℤ) [ZMOD p] := by parley_subst_at c1 s5_13_2_1
          exact row1
        -- 5.13.2.3. mun:congruent-in-range, from 5.10, 5.11, 5.13.2.2
        have s5_13_2_3 : (0 : ℤ) = 1 := (Parley.Items.Stdlib.Divisibility.mun_congruent_in_range (n := p) (by parley_set_side) (x := (0 : ℤ)) s5_10 (y := (1 : ℤ)) s5_11 s5_13_2_2)
        exact absurd s5_13_2_3 (by norm_num)
      -- 5.13.3. contradiction
      have s5_13_3 : f a ≠ 1 := by
        intro hS2
        -- 5.13.3.1. substitute f(a) = 1 (S2) into line 5.7
        have s5_13_3_1 : a ≡ (1 : ℤ) [ZMOD p] := by
          have at0 := (s5_7 a (by parley_set_side))
          parley_subst_at hS2 at0
        -- 5.13.3.2. mun:congruent-in-range, from 5.11, 5.13.1, 5.13.3.1
        have s5_13_3_2 : a = 1 := (Parley.Items.Stdlib.Divisibility.mun_congruent_in_range (n := p) (by parley_set_side) (x := a) s5_13_1 (y := (1 : ℤ)) s5_11 s5_13_3_1)
        -- 5.13.3.3. inequalities
        have s5_13_3_3 : a ≤ 1 := by parley_order
        -- 5.13.3.4. inequalities, from K7
        have s5_13_3_4 : ¬ a ≤ 1 := by parley_set_side
        exact s5_13_3_4 s5_13_3_3
      -- 5.13.4. contradiction
      have s5_13_4 : f a ≠ p - 1 := by
        intro hS3
        -- 5.13.4.1. substitute f(a) = p − 1 (S3) into line 5.7
        have s5_13_4_1 : a * (p - 1) ≡ (1 : ℤ) [ZMOD p] := by
          have at0 := (s5_7 a (by parley_set_side))
          parley_subst_at hS3 at0
        -- 5.13.4.2. def:congruent-mod, from 5.13.4.1
        have s5_13_4_2 : p ∣ a * (p - 1) - 1 := ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := p) (a := a * (p - 1)) (b := (1 : ℤ)))).mp s5_13_4_1
        -- 5.13.4.3. mun:divides-multiple e := p, a := p, x := a
        have r511_1 : p ∣ p := by exact (Parley.Items.Stdlib.Divisibility.mun_divides_self (n := p))
        have s5_13_4_3 : p ∣ p * a := by exact (Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := p) (a := p) (x := a) r511_1)
        -- 5.13.4.4. mun:divides-difference, from 5.13.4.2, 5.13.4.3
        have s5_13_4_4 : p ∣ p * a - (a * (p - 1) - 1) := by exact (Parley.Items.Stdlib.Divisibility.mun_divides_difference (d := p) (a := p * a) (b := a * (p - 1) - 1) s5_13_4_3 s5_13_4_2)
        -- 5.13.4.5. substitute
        have s5_13_4_5 : p ∣ a + 1 := by
          have c1 : p * a - (a * (p - 1) - 1) = a + 1 := by parley_ring
          have row1 : p ∣ a + 1 := by parley_subst_at c1 s5_13_4_4
          exact row1
        -- 5.13.4.6. restate 5.9
        have s5_13_4_6 : ¬ p ∣ a + 1 := by parley_set_side
        exact s5_13_4_6 s5_13_4_5
      -- 5.13.5. inequalities, from 5.5, 5.6, 5.13.2
      have s5_13_5 : 0 < f a := by have := (s5_5 a (by parley_set_side)); parley_order
      -- 5.13.6. mun:pos-int-nat m := f(a), from 5.6, 5.13.5
      have s5_13_6 : 0 < f a := by exact (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := f a) s5_13_5)
      -- 5.13.7. inequalities, from 5.13.3, 5.13.6
      have s5_13_7 : 1 < f a := by parley_order
      -- 5.13.8. mun:integer-step m := 1, n := f(a), from 5.6, 5.13.7
      have s5_13_8 : 1 + 1 ≤ f a := (Parley.Items.Stdlib.Numbers.mun_integer_step (m := (1 : ℤ)) (n := f a) s5_13_7)
      -- 5.13.9. substitute 1 + 1 = 2 (arithmetic) into line 5.13.8
      have s5_13_9 : 2 ≤ f a := by parley_subst_at (show (1 + 1 : ℤ) = 2 by parley_set_side) s5_13_8
      -- 5.13.10. inequalities, from 5.5, 5.13.4
      have s5_13_10 : f a < p - 1 := by have := (s5_5 a (by parley_set_side)); parley_order
      -- 5.13.11. mun:integer-step m := f(a), n := p − 1, from 5.6, 5.13.10
      have s5_13_11 : f a + 1 ≤ p - 1 := by exact (Parley.Items.Stdlib.Numbers.mun_integer_step (m := f a) (n := p - 1) s5_13_10)
      -- 5.13.12. inequalities
      have s5_13_12 : f a ≤ p - 2 := by parley_order
      -- 5.13.13. def:range-between k := f(a), a := 2, b := p − 2, from 5.6, 5.13.9, 5.13.12
      exact ((Parley.Items.Stdlib.Sums.def_range_between (k := f a) (a := (2 : ℤ)) (b := p - 2))).mpr (by parley_set_side)
    -- 5.14. proof
    have s5_14 : ∀ a : ℤ, a ∈ Finset.Icc 2 (p - 2) → f a ≠ a := by
      intro a hK8
      try push_cast at hK8
      try have hK8_bounds := Finset.mem_Icc.mp hK8
      intro hS4
      -- 5.14.1. substitute f(a) = a (S4) into line 5.7
      have s5_14_1 : a * a ≡ (1 : ℤ) [ZMOD p] := by
        have at0 := (s5_7 a (by parley_set_side))
        parley_subst_at hS4 at0
      -- 5.14.2. def:congruent-mod, from 5.14.1
      have s5_14_2 : p ∣ a * a - 1 := ((Parley.Items.Stdlib.Divisibility.def_congruent_mod (n := p) (a := a * a) (b := (1 : ℤ)))).mp s5_14_1
      -- 5.14.3. substitute
      have s5_14_3 : p ∣ (a - 1) * (a + 1) := by
        have c1 : a * a - 1 = (a - 1) * (a + 1) := by parley_ring
        have row1 : p ∣ (a - 1) * (a + 1) := by parley_subst_at c1 s5_14_2
        exact row1
      -- 5.14.4. thm:prime-divides-product m := a − 1, n := a + 1, from H2, 5.14.3
      have s5_14_4 : p ∣ a - 1 ∨ p ∣ a + 1 := ((Parley.Items.Stdlib.Divisibility.thm_prime_divides_product (p := p) (by parley_set_side) hH2 (m := a - 1) (n := a + 1))).mp s5_14_3
      -- 5.14.5. mun:disjunctive-syllogism-left, from 5.8, 5.14.4
      have s5_14_5 : p ∣ a + 1 := by exact (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism_left (P := p ∣ a - 1) (Q := p ∣ a + 1) s5_14_4 (s5_8 a (by parley_set_side)))
      -- 5.14.6. restate 5.9
      have s5_14_6 : ¬ p ∣ a + 1 := by parley_set_side
      exact s5_14_6 s5_14_5
    -- 5.15. proof
    have s5_15 : ∀ a : ℤ, a ∈ Finset.Icc 2 (p - 2) → f (f a) = a := by
      intro a hK9
      try push_cast at hK9
      try have hK9_bounds := Finset.mem_Icc.mp hK9
      -- 5.15.1. instantiate a := f(a) in line 5.5, from 5.13
      have s5_15_1 : f (f a) ∈ Finset.Icc (0 : ℤ) (p - 1) := by exact (s5_5 (f a) (by parley_set_side))
      -- 5.15.2. mun:range-integer, from 5.15.1
      -- 5.15.3. algebra, from 5.6, 5.15.2
      have s5_15_3 : f (f a) * f a = f a * f (f a) := by parley_ring
      -- 5.15.4. calculation
      have s5_15_4 : f (f a) * f a ≡ a * f a [ZMOD p] := by
        calc f (f a) * f a = f a * f (f a) := by parley_set_side
          _ ≡ 1 [ZMOD p] := by exact (s5_7 (f a) (by parley_set_side))
          _ ≡ a * f a [ZMOD p] := by first | exact (s5_7 a (by parley_set_side)) | exact ((s5_7 a (by parley_set_side))).symm | parley_set_side
      -- 5.15.5. instantiate a := f(a) in line 5.4, from 5.13
      have s5_15_5 : (Int.gcd (f a) p : ℤ) = 1 := by exact (s5_4 (f a) (by parley_set_side))
      -- 5.15.6. thm:congruent-cancel c := f(a), from 5.6, 5.15.2, 5.15.4, 5.15.5
      have s5_15_6 : f (f a) ≡ a [ZMOD p] := by exact (Parley.Items.Stdlib.Divisibility.thm_congruent_cancel (x := f (f a)) (y := a) (c := f a) (n := p) (by parley_set_side) s5_15_4 s5_15_5)
      -- 5.15.7. mun:in-subset, from K9, 5.12
      have s5_15_7 : a ∈ Finset.Icc (0 : ℤ) (p - 1) := by first | exact (Parley.Items.Stdlib.Sets.mun_in_subset (X := (Set.Icc (2 : ℤ) (p - 2) : Set ℤ)) (Y := (Set.Icc (0 : ℤ) (p - 1) : Set ℤ)) (u := a) (by parley_whole_side) (by parley_whole_side)) | exact ((Parley.Items.Stdlib.Sets.mun_in_subset (X := (Set.Icc (2 : ℤ) (p - 2) : Set ℤ)) (Y := (Set.Icc (0 : ℤ) (p - 1) : Set ℤ)) (u := a) (by parley_whole_side) (by parley_whole_side))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_in_subset (X := (Set.Icc (2 : ℤ) (p - 2) : Set ℤ)) (Y := (Set.Icc (0 : ℤ) (p - 1) : Set ℤ)) (u := a) (by parley_whole_side) (by parley_whole_side)) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_in_subset (X := (Set.Icc (2 : ℤ) (p - 2) : Set ℤ)) (Y := (Set.Icc (0 : ℤ) (p - 1) : Set ℤ)) (u := a) (by parley_whole_side) (by parley_whole_side)) | (have h := (Parley.Items.Stdlib.Sets.mun_in_subset (X := (Set.Icc (2 : ℤ) (p - 2) : Set ℤ)) (Y := (Set.Icc (0 : ℤ) (p - 1) : Set ℤ)) (u := a) (by parley_whole_side) (by parley_whole_side)); parley_set_side)
      -- 5.15.8. mun:congruent-in-range, from 5.15.1, 5.15.6, 5.15.7
      exact (Parley.Items.Stdlib.Divisibility.mun_congruent_in_range (n := p) (by parley_set_side) (x := f (f a)) s5_15_1 (y := a) s5_15_7 s5_15_6)
    -- 5.16. mun:function-into, from D1, 5.13
    have s5_16 : Set.MapsTo f (Set.Icc (2 : ℤ) (p - 2) : Set ℤ) (Set.Icc (2 : ℤ) (p - 2) : Set ℤ) := by exact (Parley.Items.Stdlib.Functions.mun_function_into (E := f) (X := (Set.Icc (2 : ℤ) (p - 2) : Set ℤ)) (Y := (Set.Icc (2 : ℤ) (p - 2) : Set ℤ)) (by parley_set_side) (by parley_whole_side))
    -- 5.17. mun:range-finite
    have s5_17 : (Set.Icc (2 : ℤ) (p - 2) : Set ℤ).Finite := by exact (Parley.Items.Stdlib.Sums.mun_range_finite (a := (2 : ℤ)) (b := p - 2))
    -- 5.18. mun:range-in-integers
    have s5_18 : (Set.Icc (2 : ℤ) (p - 2) : Set ℤ) ⊆ (Set.univ : Set ℤ) := by exact (Parley.Items.Stdlib.Sums.mun_range_in_integers (a := (2 : ℤ)) (b := p - 2))
    -- 5.19. thm:paired-product, from 5.7, 5.14, 5.15, 5.17, 5.18
    have r628_1 : Set.MapsTo f (Set.Icc (2 : ℤ) (p - 2) : Set ℤ) (Set.Icc (2 : ℤ) (p - 2) : Set ℤ) := by parley_set_side
    have s5_19 : (∏ a ∈ Finset.Icc (2 : ℤ) (p - 2), (a : ℤ)) ≡ (1 : ℤ) [ZMOD p] := by first | exact (Parley.Proofs.Wiedijk.Wilson.PairedProduct.paired_product (X := (Set.Icc (2 : ℤ) (p - 2) : Set ℤ)) (by parley_whole_side) (by parley_whole_side) (n := p) (by parley_set_side) (f := f) (by parley_whole_side) (by parley_whole_side) (by parley_whole_side) (by parley_whole_side)) | exact ((Parley.Proofs.Wiedijk.Wilson.PairedProduct.paired_product (X := (Set.Icc (2 : ℤ) (p - 2) : Set ℤ)) (by parley_whole_side) (by parley_whole_side) (n := p) (by parley_set_side) (f := f) (by parley_whole_side) (by parley_whole_side) (by parley_whole_side) (by parley_whole_side))).symm | simpa using (Parley.Proofs.Wiedijk.Wilson.PairedProduct.paired_product (X := (Set.Icc (2 : ℤ) (p - 2) : Set ℤ)) (by parley_whole_side) (by parley_whole_side) (n := p) (by parley_set_side) (f := f) (by parley_whole_side) (by parley_whole_side) (by parley_whole_side) (by parley_whole_side)) | exact_mod_cast (Parley.Proofs.Wiedijk.Wilson.PairedProduct.paired_product (X := (Set.Icc (2 : ℤ) (p - 2) : Set ℤ)) (by parley_whole_side) (by parley_whole_side) (n := p) (by parley_set_side) (f := f) (by parley_whole_side) (by parley_whole_side) (by parley_whole_side) (by parley_whole_side)) | (have h := (Parley.Proofs.Wiedijk.Wilson.PairedProduct.paired_product (X := (Set.Icc (2 : ℤ) (p - 2) : Set ℤ)) (by parley_whole_side) (by parley_whole_side) (n := p) (by parley_set_side) (f := f) (by parley_whole_side) (by parley_whole_side) (by parley_whole_side) (by parley_whole_side)); rw [← Finset.coe_Icc, finprod_mem_coe_finset] at h; exact h) | (have h := (Parley.Proofs.Wiedijk.Wilson.PairedProduct.paired_product (X := (Set.Icc (2 : ℤ) (p - 2) : Set ℤ)) (by parley_whole_side) (by parley_whole_side) (n := p) (by parley_set_side) (f := f) (by parley_whole_side) (by parley_whole_side) (by parley_whole_side) (by parley_whole_side)); parley_set_side)
    -- 5.20. mun:nat-minus-one n := p
    have s5_20 : 0 ≤ p - 1 := by exact (Parley.Items.Stdlib.Numbers.mun_nat_minus_one (n := p) (by parley_set_side))
    -- 5.21. mun:factorial-product n := p − 1, from 5.20
    have s5_21 : (LeanBridges.Counting.factorial (p - 1) : ℤ) = (∏ k ∈ Finset.Icc (1 : ℤ) (p - 1), (k : ℤ)) := by exact (Parley.Items.Stdlib.Counting.mun_factorial_product (n := p - 1) (by parley_set_side))
    -- 5.22. mun:product-extended a := 1, n := p − 2
    have r638_1 : p - 2 ≥ 1 := by parley_order
    have s5_22 : (∏ k ∈ Finset.Icc (1 : ℤ) (p - 2 + 1), (k : ℤ)) = (∏ k ∈ Finset.Icc (1 : ℤ) (p - 2), (k : ℤ)) * (p - 2 + 1) := (Parley.Items.Stdlib.Sums.mun_product_extended (t := (fun k : ℤ => k)) (a := (1 : ℤ)) (n := p - 2) r638_1)
    -- 5.23. substitute
    have s5_23 : (∏ k ∈ Finset.Icc (1 : ℤ) (p - 1), (k : ℤ)) = (∏ k ∈ Finset.Icc (1 : ℤ) (p - 2), (k : ℤ)) * (p - 1) := by
      have c1 : p - 2 + 1 = p - 1 := by parley_ring
      have row1 : (∏ k ∈ Finset.Icc (1 : ℤ) (p - 1), (k : ℤ)) = (∏ k ∈ Finset.Icc (1 : ℤ) (p - 2), (k : ℤ)) * (p - 1) := by parley_subst_at c1 s5_22
      exact row1
    -- 5.24. mun:product-first a := 1, b := p − 2
    have r647_1 : 1 ≤ p - 2 := by parley_order
    have s5_24 : (∏ k ∈ Finset.Icc (1 : ℤ) (p - 2), (k : ℤ)) = 1 * (∏ k ∈ Finset.Icc (1 + 1 : ℤ) (p - 2), (k : ℤ)) := (Parley.Items.Stdlib.Sums.mun_product_first (t := (fun k : ℤ => k)) (a := (1 : ℤ)) (b := p - 2) r647_1)
    -- 5.25. mun:product-integer, from 5.17, 5.18
    -- 5.26. substitute 1 + 1 = 2 (arithmetic) into line 5.24
    have s5_26 : (∏ k ∈ Finset.Icc (1 : ℤ) (p - 2), (k : ℤ)) = (∏ k ∈ Finset.Icc (2 : ℤ) (p - 2), (k : ℤ)) := by parley_subst_at (show (1 + 1 : ℤ) = 2 by parley_set_side) s5_24
    -- 5.27. substitute ∏(k = 1 to p − 2) k = ∏(k = 2 to p − 2) k (line 5.26)
    have s5_27 : (∏ k ∈ Finset.Icc (1 : ℤ) (p - 2), (k : ℤ)) * (p - 1) = (∏ k ∈ Finset.Icc (2 : ℤ) (p - 2), (k : ℤ)) * (p - 1) := by parley_subst s5_26
    -- 5.28. thm:congruent-times b := 1, c := p − 1, from 5.19, 5.25
    have s5_28 : (∏ k ∈ Finset.Icc (2 : ℤ) (p - 2), (k : ℤ)) * (p - 1) ≡ p - 1 [ZMOD p] := by first | exact (Parley.Proofs.Wiedijk.DivisibilityByThree.CongruentTimes.congruent_times (a := ∏ k ∈ Finset.Icc (2 : ℤ) (p - 2), (k : ℤ)) (b := (1 : ℤ)) (c := p - 1) (n := p) (by parley_set_side) s5_19) | exact ((Parley.Proofs.Wiedijk.DivisibilityByThree.CongruentTimes.congruent_times (a := ∏ k ∈ Finset.Icc (2 : ℤ) (p - 2), (k : ℤ)) (b := (1 : ℤ)) (c := p - 1) (n := p) (by parley_set_side) s5_19)).symm | simpa using (Parley.Proofs.Wiedijk.DivisibilityByThree.CongruentTimes.congruent_times (a := ∏ k ∈ Finset.Icc (2 : ℤ) (p - 2), (k : ℤ)) (b := (1 : ℤ)) (c := p - 1) (n := p) (by parley_set_side) s5_19) | exact_mod_cast (Parley.Proofs.Wiedijk.DivisibilityByThree.CongruentTimes.congruent_times (a := ∏ k ∈ Finset.Icc (2 : ℤ) (p - 2), (k : ℤ)) (b := (1 : ℤ)) (c := p - 1) (n := p) (by parley_set_side) s5_19) | (have h := (Parley.Proofs.Wiedijk.DivisibilityByThree.CongruentTimes.congruent_times (a := ∏ k ∈ Finset.Icc (2 : ℤ) (p - 2), (k : ℤ)) (b := (1 : ℤ)) (c := p - 1) (n := p) (by parley_set_side) s5_19); parley_set_side)
    -- 5.29. calculation
    calc (LeanBridges.Counting.factorial (p - 1) : ℤ) = (∏ k ∈ Finset.Icc (1 : ℤ) (p - 1), (k : ℤ)) := by parley_set_side
      _ = (∏ k ∈ Finset.Icc (1 : ℤ) (p - 2), (k : ℤ)) * (p - 1) := by parley_set_side
      _ = (∏ k ∈ Finset.Icc (2 : ℤ) (p - 2), (k : ℤ)) * (p - 1) := by parley_set_side
      _ ≡ p - 1 [ZMOD p] := by parley_set_side
      _ ≡ -1 [ZMOD p] := by exact (Parley.Items.Stdlib.Divisibility.mun_minus_one_congruent (n := p) (by parley_set_side))
  · skip
    -- 5.30. arithmetic
    have s5_30 : (LeanBridges.Counting.factorial (2 - 1 : ℤ) : ℤ) ≡ (-1 : ℤ) [ZMOD (2 : ℤ)] := by parley_arith
    -- 5.31. substitute 2 = p (C2) into line 5.30
    have r680_1 : 0 ≤ p - 1 := by exact (Parley.Items.Stdlib.Numbers.mun_nat_minus_one (n := p) (by parley_set_side))
    parley_subst_at hC2 s5_30

end Parley.Proofs.Wiedijk.Wilson.Wilson
