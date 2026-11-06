module

public import AlgebraTactics
public import Counting
public import FactorialTactics
public import Functions
public import PowerTactics
public import SetTactics
public import SubstTactics
public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Data.ENat.Defs
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Reasoning
public import Parley.Items.Stdlib.Sets
public import Parley.Proofs.Wiedijk.Ramsey.OnePointPart
public import Parley.Proofs.Wiedijk.Ramsey.RamseyStep

/-! Written from proofs/wiedijk/ramsey.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.Ramsey.Ramsey

set_option maxHeartbeats 600000 in
theorem ramsey {α : Type*} (V : Set α) (E : Set (Set α)) (F : Set (Set α)) (r : ℤ) (hH1 : 0 < r) (s : ℤ) (hH2 : 0 < s) (hH4 : V.Finite) (hH7 : ∀ Y ∈ 𝒫 V, Y.encard = ((2 : ℕ) : ℕ∞) → Y ∈ E ∨ Y ∈ F) (hH8 : (LeanBridges.Counting.choose (r + s - 2) (r - 1) : ℤ) ≤ (V.ncard : ℤ)) :
    (∃ W ∈ 𝒫 V, ((r.toNat : ℕ) : ℕ∞) ≤ W.encard ∧ (∀ Y ∈ 𝒫 W, Y.encard = ((2 : ℕ) : ℕ∞) → Y ∈ E) ∨ ((s.toNat : ℕ) : ℕ∞) ≤ W.encard ∧ (∀ Y ∈ 𝒫 W, Y.encard = ((2 : ℕ) : ℕ∞) → Y ∈ F)) := by
  -- 1. induction on k starting at 1
  have s1 : ∀ k : ℤ, 0 < k → (∀ j : ℤ, 0 < j → (∀ X ∈ 𝒫 V, (LeanBridges.Counting.choose (k + j - 2) (k - 1) : ℤ) ≤ (X.ncard : ℤ) → (∃ W ∈ 𝒫 X, ((k.toNat : ℕ) : ℕ∞) ≤ W.encard ∧ (∀ Y ∈ 𝒫 W, Y.encard = ((2 : ℕ) : ℕ∞) → Y ∈ E) ∨ ((j.toNat : ℕ) : ℕ∞) ≤ W.encard ∧ (∀ Y ∈ 𝒫 W, Y.encard = ((2 : ℕ) : ℕ∞) → Y ∈ F)))) := by
    intro k h_k
    replace h_k : 1 ≤ k := by omega
    induction k, h_k using LeanBridges.Functions.le_induction with
    | base =>
      intro j hK1
      intro X hK2
      intro hC1
      -- 1.1. algebra
      have s1_1 : 1 + j - 2 = j - 1 := by parley_ring
      -- 1.2. mun:finite-part, from H4, K2
      have s1_2 : X.Finite := by first | exact (Parley.Items.Stdlib.Counting.mun_finite_part (X := V) (Y := X) hH4 hK2) | exact ((Parley.Items.Stdlib.Counting.mun_finite_part (X := V) (Y := X) hH4 hK2)).symm | simpa using (Parley.Items.Stdlib.Counting.mun_finite_part (X := V) (Y := X) hH4 hK2) | exact_mod_cast (Parley.Items.Stdlib.Counting.mun_finite_part (X := V) (Y := X) hH4 hK2) | (have h := (Parley.Items.Stdlib.Counting.mun_finite_part (X := V) (Y := X) hH4 hK2); parley_set_side)
      -- 1.3. calculation
      have r559_1 : 0 ≤ j - 1 := by first | exact (Parley.Items.Stdlib.Numbers.mun_nat_minus_one (n := j) (by parley_set_side)) | exact ((Parley.Items.Stdlib.Numbers.mun_nat_minus_one (n := j) (by parley_set_side))).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_nat_minus_one (n := j) (by parley_set_side)) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_nat_minus_one (n := j) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_nat_minus_one (n := j) (by parley_set_side)); parley_set_side)
      have s1_3 : ((1 : ℕ) : ℕ∞) ≤ X.encard := by parley_count_after (by
        calc (1 : ℤ) = (LeanBridges.Counting.choose (j - 1) (0 : ℤ) : ℤ) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := j - 1) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := j - 1) (by parley_set_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := j - 1) (by parley_set_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := j - 1) (by parley_set_side)) | exact_mod_cast ((Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := j - 1) (by parley_set_side))).symm | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := j - 1) (by parley_set_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := j - 1) (by parley_set_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := j - 1) (by parley_set_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := j - 1) (by parley_set_side)); parley_set_side)
          _ = (LeanBridges.Counting.choose (j - 1) (1 - 1 : ℤ) : ℤ) := by norm_num
          _ = (LeanBridges.Counting.choose (1 + j - 2) (1 - 1 : ℤ) : ℤ) := by parley_subst s1_1
          _ ≤ (X.ncard : ℤ) := by parley_set_side)
      -- 1.4. obtain W: thm:one-point-part G := E, from 1.2, 1.3
      obtain ⟨W, s1_4a, ⟨s1_4b, _⟩⟩ := (Parley.Proofs.Wiedijk.Ramsey.OnePointPart.one_point_part (X := X) (G := E) s1_2 s1_3)
      -- 1.5. mun:or-left, from 1.4
      have s1_5 : ((1 : ℕ) : ℕ∞) ≤ W.encard ∧ (∀ Y ∈ 𝒫 W, Y.encard = ((2 : ℕ) : ℕ∞) → Y ∈ E) ∨ ((j.toNat : ℕ) : ℕ∞) ≤ W.encard ∧ (∀ Y ∈ 𝒫 W, Y.encard = ((2 : ℕ) : ℕ∞) → Y ∈ F) := by first | exact (Parley.Items.Stdlib.Reasoning.mun_or_left (P := ((1 : ℕ) : ℕ∞) ≤ W.encard ∧ (∀ Y ∈ 𝒫 W, Y.encard = ((2 : ℕ) : ℕ∞) → Y ∈ E)) (Q := ((j.toNat : ℕ) : ℕ∞) ≤ W.encard ∧ (∀ Y ∈ 𝒫 W, Y.encard = ((2 : ℕ) : ℕ∞) → Y ∈ F)) (by parley_set_side)) | exact ((Parley.Items.Stdlib.Reasoning.mun_or_left (P := ((1 : ℕ) : ℕ∞) ≤ W.encard ∧ (∀ Y ∈ 𝒫 W, Y.encard = ((2 : ℕ) : ℕ∞) → Y ∈ E)) (Q := ((j.toNat : ℕ) : ℕ∞) ≤ W.encard ∧ (∀ Y ∈ 𝒫 W, Y.encard = ((2 : ℕ) : ℕ∞) → Y ∈ F)) (by parley_set_side))).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_or_left (P := ((1 : ℕ) : ℕ∞) ≤ W.encard ∧ (∀ Y ∈ 𝒫 W, Y.encard = ((2 : ℕ) : ℕ∞) → Y ∈ E)) (Q := ((j.toNat : ℕ) : ℕ∞) ≤ W.encard ∧ (∀ Y ∈ 𝒫 W, Y.encard = ((2 : ℕ) : ℕ∞) → Y ∈ F)) (by parley_set_side)) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_or_left (P := ((1 : ℕ) : ℕ∞) ≤ W.encard ∧ (∀ Y ∈ 𝒫 W, Y.encard = ((2 : ℕ) : ℕ∞) → Y ∈ E)) (Q := ((j.toNat : ℕ) : ℕ∞) ≤ W.encard ∧ (∀ Y ∈ 𝒫 W, Y.encard = ((2 : ℕ) : ℕ∞) → Y ∈ F)) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Reasoning.mun_or_left (P := ((1 : ℕ) : ℕ∞) ≤ W.encard ∧ (∀ Y ∈ 𝒫 W, Y.encard = ((2 : ℕ) : ℕ∞) → Y ∈ E)) (Q := ((j.toNat : ℕ) : ℕ∞) ≤ W.encard ∧ (∀ Y ∈ 𝒫 W, Y.encard = ((2 : ℕ) : ℕ∞) → Y ∈ F)) (by parley_set_side)); simp (disch := omega) only [← zpow_natCast, Int.toNat_of_nonneg] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Reasoning.mun_or_left (P := ((1 : ℕ) : ℕ∞) ≤ W.encard ∧ (∀ Y ∈ 𝒫 W, Y.encard = ((2 : ℕ) : ℕ∞) → Y ∈ E)) (Q := ((j.toNat : ℕ) : ℕ∞) ≤ W.encard ∧ (∀ Y ∈ 𝒫 W, Y.encard = ((2 : ℕ) : ℕ∞) → Y ∈ F)) (by parley_set_side)); simp +contextual (disch := (simp only [Finset.mem_Icc] at *; first | omega | positivity | nlinarith)) only [parley_zpow_toNat] at h ⊢; first | exact h | exact_mod_cast h | linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Reasoning.mun_or_left (P := ((1 : ℕ) : ℕ∞) ≤ W.encard ∧ (∀ Y ∈ 𝒫 W, Y.encard = ((2 : ℕ) : ℕ∞) → Y ∈ E)) (Q := ((j.toNat : ℕ) : ℕ∞) ≤ W.encard ∧ (∀ Y ∈ 𝒫 W, Y.encard = ((2 : ℕ) : ℕ∞) → Y ∈ F)) (by parley_set_side)); parley_set_side)
      -- 1.6. exhibit, from 1.4, 1.5
      have s1_6 : ∃ W ∈ 𝒫 X, ((1 : ℕ) : ℕ∞) ≤ W.encard ∧ (∀ Y ∈ 𝒫 W, Y.encard = ((2 : ℕ) : ℕ∞) → Y ∈ E) ∨ ((j.toNat : ℕ) : ℕ∞) ≤ W.encard ∧ (∀ Y ∈ 𝒫 W, Y.encard = ((2 : ℕ) : ℕ∞) → Y ∈ F) := ⟨W, by parley_set_side, by parley_set_side⟩
      all_goals parley_set_side
    | succ k hK3 hIH1 =>
      -- 1.7. algebra
      have s1_7 : k + 1 - 1 = k := by parley_ring
      -- 1.8. induction on j starting at 1
      have s1_8 : ∀ j : ℤ, 0 < j → (∀ X ∈ 𝒫 V, (LeanBridges.Counting.choose (k + 1 + j - 2) (k + 1 - 1) : ℤ) ≤ (X.ncard : ℤ) → (∃ W ∈ 𝒫 X, (((k + 1).toNat : ℕ) : ℕ∞) ≤ W.encard ∧ (∀ Y ∈ 𝒫 W, Y.encard = ((2 : ℕ) : ℕ∞) → Y ∈ E) ∨ ((j.toNat : ℕ) : ℕ∞) ≤ W.encard ∧ (∀ Y ∈ 𝒫 W, Y.encard = ((2 : ℕ) : ℕ∞) → Y ∈ F))) := by
        intro j h_j
        replace h_j : 1 ≤ j := by omega
        induction j, h_j using LeanBridges.Functions.le_induction with
        | base =>
          intro X hK4
          intro hC2
          -- 1.8.1. algebra
          have s1_8_1 : k + 1 + 1 - 2 = k := by parley_ring
          -- 1.8.2. mun:finite-part, from H4, K4
          have s1_8_2 : X.Finite := by first | exact (Parley.Items.Stdlib.Counting.mun_finite_part (X := V) (Y := X) hH4 hK4) | exact ((Parley.Items.Stdlib.Counting.mun_finite_part (X := V) (Y := X) hH4 hK4)).symm | simpa using (Parley.Items.Stdlib.Counting.mun_finite_part (X := V) (Y := X) hH4 hK4) | exact_mod_cast (Parley.Items.Stdlib.Counting.mun_finite_part (X := V) (Y := X) hH4 hK4) | (have h := (Parley.Items.Stdlib.Counting.mun_finite_part (X := V) (Y := X) hH4 hK4); parley_set_side)
          -- 1.8.3. calculation
          have s1_8_3 : ((1 : ℕ) : ℕ∞) ≤ X.encard := by parley_count_after (by
            calc (1 : ℤ) = (LeanBridges.Counting.choose k k : ℤ) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.mun_binomial_all (n := k) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_all (n := k) (by parley_set_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_all (n := k) (by parley_set_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Counting.mun_binomial_all (n := k) (by parley_set_side)) | exact_mod_cast ((Parley.Items.Stdlib.Counting.mun_binomial_all (n := k) (by parley_set_side))).symm | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_all (n := k) (by parley_set_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_all (n := k) (by parley_set_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_all (n := k) (by parley_set_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_all (n := k) (by parley_set_side)); parley_set_side)
              _ = (LeanBridges.Counting.choose k (k + 1 - 1) : ℤ) := by parley_subst s1_7
              _ = (LeanBridges.Counting.choose (k + 1 + 1 - 2) (k + 1 - 1) : ℤ) := by parley_subst s1_8_1
              _ ≤ (X.ncard : ℤ) := by parley_set_side)
          -- 1.8.4. obtain W: thm:one-point-part G := F, from 1.8.2, 1.8.3
          obtain ⟨W, s1_8_4a, ⟨s1_8_4b, _⟩⟩ := (Parley.Proofs.Wiedijk.Ramsey.OnePointPart.one_point_part (X := X) (G := F) s1_8_2 s1_8_3)
          -- 1.8.5. mun:or-right, from 1.8.4
          have s1_8_5 : (((k + 1).toNat : ℕ) : ℕ∞) ≤ W.encard ∧ (∀ Y ∈ 𝒫 W, Y.encard = ((2 : ℕ) : ℕ∞) → Y ∈ E) ∨ ((1 : ℕ) : ℕ∞) ≤ W.encard ∧ (∀ Y ∈ 𝒫 W, Y.encard = ((2 : ℕ) : ℕ∞) → Y ∈ F) := by first | exact (Parley.Items.Stdlib.Reasoning.mun_or_right (P := (((k + 1).toNat : ℕ) : ℕ∞) ≤ W.encard ∧ (∀ Y ∈ 𝒫 W, Y.encard = ((2 : ℕ) : ℕ∞) → Y ∈ E)) (Q := ((1 : ℕ) : ℕ∞) ≤ W.encard ∧ (∀ Y ∈ 𝒫 W, Y.encard = ((2 : ℕ) : ℕ∞) → Y ∈ F)) (by parley_set_side)) | exact ((Parley.Items.Stdlib.Reasoning.mun_or_right (P := (((k + 1).toNat : ℕ) : ℕ∞) ≤ W.encard ∧ (∀ Y ∈ 𝒫 W, Y.encard = ((2 : ℕ) : ℕ∞) → Y ∈ E)) (Q := ((1 : ℕ) : ℕ∞) ≤ W.encard ∧ (∀ Y ∈ 𝒫 W, Y.encard = ((2 : ℕ) : ℕ∞) → Y ∈ F)) (by parley_set_side))).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_or_right (P := (((k + 1).toNat : ℕ) : ℕ∞) ≤ W.encard ∧ (∀ Y ∈ 𝒫 W, Y.encard = ((2 : ℕ) : ℕ∞) → Y ∈ E)) (Q := ((1 : ℕ) : ℕ∞) ≤ W.encard ∧ (∀ Y ∈ 𝒫 W, Y.encard = ((2 : ℕ) : ℕ∞) → Y ∈ F)) (by parley_set_side)) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_or_right (P := (((k + 1).toNat : ℕ) : ℕ∞) ≤ W.encard ∧ (∀ Y ∈ 𝒫 W, Y.encard = ((2 : ℕ) : ℕ∞) → Y ∈ E)) (Q := ((1 : ℕ) : ℕ∞) ≤ W.encard ∧ (∀ Y ∈ 𝒫 W, Y.encard = ((2 : ℕ) : ℕ∞) → Y ∈ F)) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Reasoning.mun_or_right (P := (((k + 1).toNat : ℕ) : ℕ∞) ≤ W.encard ∧ (∀ Y ∈ 𝒫 W, Y.encard = ((2 : ℕ) : ℕ∞) → Y ∈ E)) (Q := ((1 : ℕ) : ℕ∞) ≤ W.encard ∧ (∀ Y ∈ 𝒫 W, Y.encard = ((2 : ℕ) : ℕ∞) → Y ∈ F)) (by parley_set_side)); simp (disch := omega) only [← zpow_natCast, Int.toNat_of_nonneg] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Reasoning.mun_or_right (P := (((k + 1).toNat : ℕ) : ℕ∞) ≤ W.encard ∧ (∀ Y ∈ 𝒫 W, Y.encard = ((2 : ℕ) : ℕ∞) → Y ∈ E)) (Q := ((1 : ℕ) : ℕ∞) ≤ W.encard ∧ (∀ Y ∈ 𝒫 W, Y.encard = ((2 : ℕ) : ℕ∞) → Y ∈ F)) (by parley_set_side)); simp +contextual (disch := (simp only [Finset.mem_Icc] at *; first | omega | positivity | nlinarith)) only [parley_zpow_toNat] at h ⊢; first | exact h | exact_mod_cast h | linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Reasoning.mun_or_right (P := (((k + 1).toNat : ℕ) : ℕ∞) ≤ W.encard ∧ (∀ Y ∈ 𝒫 W, Y.encard = ((2 : ℕ) : ℕ∞) → Y ∈ E)) (Q := ((1 : ℕ) : ℕ∞) ≤ W.encard ∧ (∀ Y ∈ 𝒫 W, Y.encard = ((2 : ℕ) : ℕ∞) → Y ∈ F)) (by parley_set_side)); parley_set_side)
          -- 1.8.6. exhibit, from 1.8.4, 1.8.5
          have s1_8_6 : ∃ W ∈ 𝒫 X, (((k + 1).toNat : ℕ) : ℕ∞) ≤ W.encard ∧ (∀ Y ∈ 𝒫 W, Y.encard = ((2 : ℕ) : ℕ∞) → Y ∈ E) ∨ ((1 : ℕ) : ℕ∞) ≤ W.encard ∧ (∀ Y ∈ 𝒫 W, Y.encard = ((2 : ℕ) : ℕ∞) → Y ∈ F) := ⟨W, by parley_set_side, by parley_set_side⟩
          all_goals parley_set_side
        | succ j hK5 hIH2 =>
          -- 1.8.7. instantiate j := j + 1 in IH1
          have s1_8_7 : ∀ X ∈ 𝒫 V, (LeanBridges.Counting.choose (k + (j + 1) - 2) (k - 1) : ℤ) ≤ (X.ncard : ℤ) → (∃ W ∈ 𝒫 X, ((k.toNat : ℕ) : ℕ∞) ≤ W.encard ∧ (∀ Y ∈ 𝒫 W, Y.encard = ((2 : ℕ) : ℕ∞) → Y ∈ E) ∨ (((j + 1).toNat : ℕ) : ℕ∞) ≤ W.encard ∧ (∀ Y ∈ 𝒫 W, Y.encard = ((2 : ℕ) : ℕ∞) → Y ∈ F)) := by intro X h_X; first | exact (hIH1 (j + 1) (by parley_set_side) X (by parley_set_side)) | exact ((hIH1 (j + 1) (by parley_set_side) X (by parley_set_side))).symm | simpa using (hIH1 (j + 1) (by parley_set_side) X (by parley_set_side)) | exact_mod_cast (hIH1 (j + 1) (by parley_set_side) X (by parley_set_side)) | (have h := (hIH1 (j + 1) (by parley_set_side) X (by parley_set_side)); parley_set_side)
          -- 1.8.8. substitute
          have s1_8_8 : ∀ X ∈ 𝒫 V, (LeanBridges.Counting.choose (k + j - 1) (k - 1) : ℤ) ≤ (X.ncard : ℤ) → (∃ W ∈ 𝒫 X, ((k.toNat : ℕ) : ℕ∞) ≤ W.encard ∧ (∀ Y ∈ 𝒫 W, Y.encard = ((2 : ℕ) : ℕ∞) → Y ∈ E) ∨ (((j + 1).toNat : ℕ) : ℕ∞) ≤ W.encard ∧ (∀ Y ∈ 𝒫 W, Y.encard = ((2 : ℕ) : ℕ∞) → Y ∈ F)) := by parley_count_after (by
            have c1 : k + (j + 1) - 2 = k + j - 1 := by parley_ring
            have row1 : ∀ X ∈ 𝒫 V, (LeanBridges.Counting.choose (k + j - 1) (k - 1) : ℤ) ≤ (X.ncard : ℤ) → (∃ W ∈ 𝒫 X, ((k.toNat : ℕ) : ℕ∞) ≤ W.encard ∧ (∀ Y ∈ 𝒫 W, Y.encard = ((2 : ℕ) : ℕ∞) → Y ∈ E) ∨ (((j + 1).toNat : ℕ) : ℕ∞) ≤ W.encard ∧ (∀ Y ∈ 𝒫 W, Y.encard = ((2 : ℕ) : ℕ∞) → Y ∈ F)) := by parley_subst_at c1 s1_8_7
            exact row1)
          -- 1.8.9. algebra
          have s1_8_9 : k + 1 + j - 2 = k + j - 1 := by parley_ring
          -- 1.8.10. substitute k + 1 + j − 2 = k + j − 1 (line 1.8.9) into IH2
          have s1_8_10 : ∀ X ∈ 𝒫 V, (LeanBridges.Counting.choose (k + j - 1) (k + 1 - 1) : ℤ) ≤ (X.ncard : ℤ) → (∃ W ∈ 𝒫 X, (((k + 1).toNat : ℕ) : ℕ∞) ≤ W.encard ∧ (∀ Y ∈ 𝒫 W, Y.encard = ((2 : ℕ) : ℕ∞) → Y ∈ E) ∨ ((j.toNat : ℕ) : ℕ∞) ≤ W.encard ∧ (∀ Y ∈ 𝒫 W, Y.encard = ((2 : ℕ) : ℕ∞) → Y ∈ F)) := by intro X h_X; parley_subst_at s1_8_9 hIH2
          -- 1.8.11. substitute k + 1 − 1 = k (line 1.7) into line 1.8.10
          have s1_8_11 : ∀ X ∈ 𝒫 V, (LeanBridges.Counting.choose (k + j - 1) k : ℤ) ≤ (X.ncard : ℤ) → (∃ W ∈ 𝒫 X, (((k + 1).toNat : ℕ) : ℕ∞) ≤ W.encard ∧ (∀ Y ∈ 𝒫 W, Y.encard = ((2 : ℕ) : ℕ∞) → Y ∈ E) ∨ ((j.toNat : ℕ) : ℕ∞) ≤ W.encard ∧ (∀ Y ∈ 𝒫 W, Y.encard = ((2 : ℕ) : ℕ∞) → Y ∈ F)) := by intro X h_X; parley_subst_at s1_7 s1_8_10
          -- 1.8.12. algebra
          have s1_8_12 : k + 1 + (j + 1) - 2 = k + j := by parley_ring
          -- 1.8.13. proof
          have s1_8_13 : ∀ X ∈ 𝒫 V, (LeanBridges.Counting.choose (k + 1 + (j + 1) - 2) (k + 1 - 1) : ℤ) ≤ (X.ncard : ℤ) → (∃ W ∈ 𝒫 X, (((k + 1).toNat : ℕ) : ℕ∞) ≤ W.encard ∧ (∀ Y ∈ 𝒫 W, Y.encard = ((2 : ℕ) : ℕ∞) → Y ∈ E) ∨ (((j + 1).toNat : ℕ) : ℕ∞) ≤ W.encard ∧ (∀ Y ∈ 𝒫 W, Y.encard = ((2 : ℕ) : ℕ∞) → Y ∈ F)) := by
            intro X hK6
            intro hC3
            -- 1.8.13.1. calculation
            have s1_8_13_1 : (LeanBridges.Counting.choose (k + j) k : ℤ) ≤ (X.ncard : ℤ) := by
              calc (LeanBridges.Counting.choose (k + j) k : ℤ) = (LeanBridges.Counting.choose (k + j) (k + 1 - 1) : ℤ) := by parley_subst s1_7
                _ = (LeanBridges.Counting.choose (k + 1 + (j + 1) - 2) (k + 1 - 1) : ℤ) := by parley_subst s1_8_12
                _ ≤ (X.ncard : ℤ) := by parley_set_side
            -- 1.8.13.2. thm:ramsey-step, from H4, H7, K6, 1.8.8, 1.8.11, 1.8.13.1
            have s1_8_13_2 : ∃ W ∈ 𝒫 X, (((k + 1).toNat : ℕ) : ℕ∞) ≤ W.encard ∧ (∀ Y ∈ 𝒫 W, Y.encard = ((2 : ℕ) : ℕ∞) → Y ∈ E) ∨ (((j + 1).toNat : ℕ) : ℕ∞) ≤ W.encard ∧ (∀ Y ∈ 𝒫 W, Y.encard = ((2 : ℕ) : ℕ∞) → Y ∈ F) := by first | exact (Parley.Proofs.Wiedijk.Ramsey.RamseyStep.ramsey_step (V := V) (E := E) (F := F) (k := k) (by parley_set_side) (j := j) (by parley_set_side) hH4 hH7 (X := X) hK6 s1_8_13_1 (by parley_set_side) (by parley_set_side)) | exact ((Parley.Proofs.Wiedijk.Ramsey.RamseyStep.ramsey_step (V := V) (E := E) (F := F) (k := k) (by parley_set_side) (j := j) (by parley_set_side) hH4 hH7 (X := X) hK6 s1_8_13_1 (by parley_set_side) (by parley_set_side))).symm | simpa using (Parley.Proofs.Wiedijk.Ramsey.RamseyStep.ramsey_step (V := V) (E := E) (F := F) (k := k) (by parley_set_side) (j := j) (by parley_set_side) hH4 hH7 (X := X) hK6 s1_8_13_1 (by parley_set_side) (by parley_set_side)) | exact_mod_cast (Parley.Proofs.Wiedijk.Ramsey.RamseyStep.ramsey_step (V := V) (E := E) (F := F) (k := k) (by parley_set_side) (j := j) (by parley_set_side) hH4 hH7 (X := X) hK6 s1_8_13_1 (by parley_set_side) (by parley_set_side)) | (have h := (Parley.Proofs.Wiedijk.Ramsey.RamseyStep.ramsey_step (V := V) (E := E) (F := F) (k := k) (by parley_set_side) (j := j) (by parley_set_side) hH4 hH7 (X := X) hK6 s1_8_13_1 (by parley_set_side) (by parley_set_side)); parley_set_side)
            all_goals parley_set_side
          all_goals parley_set_side
      all_goals parley_set_side
  -- 2. mun:subset-self
  have s2 : V ⊆ V := by first | exact (Parley.Items.Stdlib.Sets.mun_subset_self (X := V)) | exact ((Parley.Items.Stdlib.Sets.mun_subset_self (X := V))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_subset_self (X := V)) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_subset_self (X := V)) | (have h := (Parley.Items.Stdlib.Sets.mun_subset_self (X := V)); parley_set_side)
  -- 3. instantiate k := r, j := s, X := V in line 1, from H8, 2
  have s3 : ∃ W ∈ 𝒫 V, ((r.toNat : ℕ) : ℕ∞) ≤ W.encard ∧ (∀ Y ∈ 𝒫 W, Y.encard = ((2 : ℕ) : ℕ∞) → Y ∈ E) ∨ ((s.toNat : ℕ) : ℕ∞) ≤ W.encard ∧ (∀ Y ∈ 𝒫 W, Y.encard = ((2 : ℕ) : ℕ∞) → Y ∈ F) := by first | exact (s1 r (by parley_set_side) s (by parley_set_side) V (by parley_set_side) (by parley_set_side)) | exact ((s1 r (by parley_set_side) s (by parley_set_side) V (by parley_set_side) (by parley_set_side))).symm | simpa using (s1 r (by parley_set_side) s (by parley_set_side) V (by parley_set_side) (by parley_set_side)) | exact_mod_cast (s1 r (by parley_set_side) s (by parley_set_side) V (by parley_set_side) (by parley_set_side)) | (have h := (s1 r (by parley_set_side) s (by parley_set_side) V (by parley_set_side) (by parley_set_side)); parley_set_side)
  all_goals exact s3

end Parley.Proofs.Wiedijk.Ramsey.Ramsey
