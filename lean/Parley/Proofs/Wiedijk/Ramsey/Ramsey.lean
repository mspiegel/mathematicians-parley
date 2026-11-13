module

public import AlgebraTactics
public import Counting
public import FactorialTactics
public import Functions
public import SetTactics
public import Tactics
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
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

theorem ramsey {α : Type*} (V : Set α) (E : Set (Set α)) (F : Set (Set α)) (r : ℤ) (hH1 : 0 < r) (s : ℤ) (hH2 : 0 < s) (hH4 : V.Finite) (hH7 : ∀ Y ∈ 𝒫 V, (Y.ncard : ℤ) = 2 → Y ∈ E ∨ Y ∈ F) (hH8 : (LeanBridges.Counting.choose (r + s - 2) (r - 1) : ℤ) ≤ (V.ncard : ℤ)) :
    (∃ W ∈ 𝒫 V, r ≤ (W.ncard : ℤ) ∧ (∀ Y ∈ 𝒫 W, (Y.ncard : ℤ) = 2 → Y ∈ E) ∨ s ≤ (W.ncard : ℤ) ∧ (∀ Y ∈ 𝒫 W, (Y.ncard : ℤ) = 2 → Y ∈ F)) := by
  -- 1. induction on k starting at 1
  have s1 : ∀ k : ℤ, 0 < k → (∀ j : ℤ, 0 < j → (∀ X ∈ 𝒫 V, (LeanBridges.Counting.choose (k + j - 2) (k - 1) : ℤ) ≤ (X.ncard : ℤ) → (∃ W ∈ 𝒫 X, k ≤ (W.ncard : ℤ) ∧ (∀ Y ∈ 𝒫 W, (Y.ncard : ℤ) = 2 → Y ∈ E) ∨ j ≤ (W.ncard : ℤ) ∧ (∀ Y ∈ 𝒫 W, (Y.ncard : ℤ) = 2 → Y ∈ F)))) := by
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
      have s1_2 : X.Finite := by exact (Parley.Items.Stdlib.Counting.mun_finite_part (X := V) (Y := X) hH4 hK2)
      -- 1.3. calculation
      have r559_1 : 0 ≤ j - 1 := by exact (Parley.Items.Stdlib.Numbers.mun_nat_minus_one (n := j) hK1)
      have s1_3 : 1 ≤ (X.ncard : ℤ) := by parley_count_after (by
        calc (1 : ℤ) = (LeanBridges.Counting.choose (j - 1) (0 : ℤ) : ℤ) := by exact (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := j - 1) r559_1).symm
          _ = (LeanBridges.Counting.choose (j - 1) (1 - 1 : ℤ) : ℤ) := by norm_num
          _ = (LeanBridges.Counting.choose (1 + j - 2) (1 - 1 : ℤ) : ℤ) := by (have h := congrArg (fun t : ℤ => (LeanBridges.Counting.choose t (1 - 1 : ℤ) : ℤ)) s1_1.symm; push_cast at h ⊢; all_goals exact_mod_cast h)
          _ ≤ (X.ncard : ℤ) := by parley_set_side)
      -- 1.4. obtain W: thm:one-point-part G := E, from 1.2, 1.3
      obtain ⟨W, s1_4a, s1_4b⟩ := (Parley.Proofs.Wiedijk.Ramsey.OnePointPart.one_point_part (X := X) (G := E) s1_2 s1_3)
      -- 1.5. mun:or-left, from 1.4
      have s1_5 : 1 ≤ (W.ncard : ℤ) ∧ (∀ Y ∈ 𝒫 W, (Y.ncard : ℤ) = 2 → Y ∈ E) ∨ j ≤ (W.ncard : ℤ) ∧ (∀ Y ∈ 𝒫 W, (Y.ncard : ℤ) = 2 → Y ∈ F) := by exact (Parley.Items.Stdlib.Reasoning.mun_or_left (P := 1 ≤ (W.ncard : ℤ) ∧ (∀ Y ∈ 𝒫 W, (Y.ncard : ℤ) = 2 → Y ∈ E)) (Q := j ≤ (W.ncard : ℤ) ∧ (∀ Y ∈ 𝒫 W, (Y.ncard : ℤ) = 2 → Y ∈ F)) s1_4b)
      -- 1.6. exhibit, from 1.4, 1.5
      exact ⟨W, s1_4a, s1_5⟩
    | succ k hK3 hIH1 =>
      -- 1.7. algebra
      have s1_7 : k + 1 - 1 = k := by parley_ring
      -- 1.8. induction on j starting at 1
      intro j h_j
      replace h_j : 1 ≤ j := by omega
      induction j, h_j using LeanBridges.Functions.le_induction with
      | base =>
        intro X hK4
        intro hC2
        -- 1.8.1. algebra
        have s1_8_1 : k + 1 + 1 - 2 = k := by parley_ring
        -- 1.8.2. mun:finite-part, from H4, K4
        have s1_8_2 : X.Finite := by exact (Parley.Items.Stdlib.Counting.mun_finite_part (X := V) (Y := X) hH4 hK4)
        -- 1.8.3. calculation
        have s1_8_3 : 1 ≤ (X.ncard : ℤ) := by parley_count_after (by
          calc (1 : ℤ) = (LeanBridges.Counting.choose k k : ℤ) := by exact (Parley.Items.Stdlib.Counting.mun_binomial_all (n := k) (le_of_lt (lt_of_lt_of_le zero_lt_one hK3))).symm
            _ = (LeanBridges.Counting.choose k (k + 1 - 1) : ℤ) := by (have h := congrArg (fun t : ℤ => (LeanBridges.Counting.choose k t : ℤ)) s1_7.symm; push_cast at h ⊢; all_goals exact_mod_cast h)
            _ = (LeanBridges.Counting.choose (k + 1 + 1 - 2) (k + 1 - 1) : ℤ) := by (have h := congrArg (fun t : ℤ => (LeanBridges.Counting.choose t (k + 1 - 1) : ℤ)) s1_8_1.symm; push_cast at h ⊢; all_goals exact_mod_cast h)
            _ ≤ (X.ncard : ℤ) := by parley_set_side)
        -- 1.8.4. obtain W: thm:one-point-part G := F, from 1.8.2, 1.8.3
        obtain ⟨W, s1_8_4a, s1_8_4b⟩ := (Parley.Proofs.Wiedijk.Ramsey.OnePointPart.one_point_part (X := X) (G := F) s1_8_2 s1_8_3)
        -- 1.8.5. mun:or-right, from 1.8.4
        have s1_8_5 : k + 1 ≤ (W.ncard : ℤ) ∧ (∀ Y ∈ 𝒫 W, (Y.ncard : ℤ) = 2 → Y ∈ E) ∨ 1 ≤ (W.ncard : ℤ) ∧ (∀ Y ∈ 𝒫 W, (Y.ncard : ℤ) = 2 → Y ∈ F) := by exact (Parley.Items.Stdlib.Reasoning.mun_or_right (P := k + 1 ≤ (W.ncard : ℤ) ∧ (∀ Y ∈ 𝒫 W, (Y.ncard : ℤ) = 2 → Y ∈ E)) (Q := 1 ≤ (W.ncard : ℤ) ∧ (∀ Y ∈ 𝒫 W, (Y.ncard : ℤ) = 2 → Y ∈ F)) s1_8_4b)
        -- 1.8.6. exhibit, from 1.8.4, 1.8.5
        exact ⟨W, s1_8_4a, s1_8_5⟩
      | succ j hK5 hIH2 =>
        -- 1.8.7. instantiate j := j + 1 in IH1
        have s1_8_7 : ∀ X ∈ 𝒫 V, (LeanBridges.Counting.choose (k + (j + 1) - 2) (k - 1) : ℤ) ≤ (X.ncard : ℤ) → (∃ W ∈ 𝒫 X, k ≤ (W.ncard : ℤ) ∧ (∀ Y ∈ 𝒫 W, (Y.ncard : ℤ) = 2 → Y ∈ E) ∨ j + 1 ≤ (W.ncard : ℤ) ∧ (∀ Y ∈ 𝒫 W, (Y.ncard : ℤ) = 2 → Y ∈ F)) := by intro X h_X; exact (hIH1 (j + 1) (add_pos (lt_of_lt_of_le zero_lt_one hK5) (by norm_num)) X h_X)
        -- 1.8.8. substitute
        have s1_8_8 : ∀ X ∈ 𝒫 V, (LeanBridges.Counting.choose (k + j - 1) (k - 1) : ℤ) ≤ (X.ncard : ℤ) → (∃ W ∈ 𝒫 X, k ≤ (W.ncard : ℤ) ∧ (∀ Y ∈ 𝒫 W, (Y.ncard : ℤ) = 2 → Y ∈ E) ∨ j + 1 ≤ (W.ncard : ℤ) ∧ (∀ Y ∈ 𝒫 W, (Y.ncard : ℤ) = 2 → Y ∈ F)) := by parley_count_after (by
          have c1 : k + (j + 1) - 2 = k + j - 1 := by parley_ring
          have row1 : ∀ X ∈ 𝒫 V, (LeanBridges.Counting.choose (k + j - 1) (k - 1) : ℤ) ≤ (X.ncard : ℤ) → (∃ W ∈ 𝒫 X, k ≤ (W.ncard : ℤ) ∧ (∀ Y ∈ 𝒫 W, (Y.ncard : ℤ) = 2 → Y ∈ E) ∨ j + 1 ≤ (W.ncard : ℤ) ∧ (∀ Y ∈ 𝒫 W, (Y.ncard : ℤ) = 2 → Y ∈ F)) := by (have h := Eq.subst (motive := (fun t : ℤ => ∀ X ∈ 𝒫 V, (LeanBridges.Counting.choose t (k - 1) : ℤ) ≤ (X.ncard : ℤ) → (∃ W ∈ 𝒫 X, k ≤ (W.ncard : ℤ) ∧ (∀ Y ∈ 𝒫 W, (Y.ncard : ℤ) = 2 → Y ∈ E) ∨ j + 1 ≤ (W.ncard : ℤ) ∧ (∀ Y ∈ 𝒫 W, (Y.ncard : ℤ) = 2 → Y ∈ F)))) c1 s1_8_7; push_cast at h ⊢; all_goals exact_mod_cast h)
          exact row1)
        -- 1.8.9. algebra
        have s1_8_9 : k + 1 + j - 2 = k + j - 1 := by parley_ring
        -- 1.8.10. substitute k + 1 + j − 2 = k + j − 1 (line 1.8.9) into IH2
        have s1_8_10 : ∀ X ∈ 𝒫 V, (LeanBridges.Counting.choose (k + j - 1) (k + 1 - 1) : ℤ) ≤ (X.ncard : ℤ) → (∃ W ∈ 𝒫 X, k + 1 ≤ (W.ncard : ℤ) ∧ (∀ Y ∈ 𝒫 W, (Y.ncard : ℤ) = 2 → Y ∈ E) ∨ j ≤ (W.ncard : ℤ) ∧ (∀ Y ∈ 𝒫 W, (Y.ncard : ℤ) = 2 → Y ∈ F)) := by (have h := Eq.subst (motive := (fun t : ℤ => ∀ X ∈ 𝒫 V, (LeanBridges.Counting.choose t (k + 1 - 1) : ℤ) ≤ (X.ncard : ℤ) → (∃ W ∈ 𝒫 X, k + 1 ≤ (W.ncard : ℤ) ∧ (∀ Y ∈ 𝒫 W, (Y.ncard : ℤ) = 2 → Y ∈ E) ∨ j ≤ (W.ncard : ℤ) ∧ (∀ Y ∈ 𝒫 W, (Y.ncard : ℤ) = 2 → Y ∈ F)))) s1_8_9 hIH2; push_cast at h ⊢; all_goals exact_mod_cast h)
        -- 1.8.11. substitute k + 1 − 1 = k (line 1.7) into line 1.8.10
        have s1_8_11 : ∀ X ∈ 𝒫 V, (LeanBridges.Counting.choose (k + j - 1) k : ℤ) ≤ (X.ncard : ℤ) → (∃ W ∈ 𝒫 X, k + 1 ≤ (W.ncard : ℤ) ∧ (∀ Y ∈ 𝒫 W, (Y.ncard : ℤ) = 2 → Y ∈ E) ∨ j ≤ (W.ncard : ℤ) ∧ (∀ Y ∈ 𝒫 W, (Y.ncard : ℤ) = 2 → Y ∈ F)) := by (have h := Eq.subst (motive := (fun t : ℤ => ∀ X ∈ 𝒫 V, (LeanBridges.Counting.choose (k + j - 1) t : ℤ) ≤ (X.ncard : ℤ) → (∃ W ∈ 𝒫 X, k + 1 ≤ (W.ncard : ℤ) ∧ (∀ Y ∈ 𝒫 W, (Y.ncard : ℤ) = 2 → Y ∈ E) ∨ j ≤ (W.ncard : ℤ) ∧ (∀ Y ∈ 𝒫 W, (Y.ncard : ℤ) = 2 → Y ∈ F)))) s1_7 s1_8_10; push_cast at h ⊢; all_goals exact_mod_cast h)
        -- 1.8.12. algebra
        have s1_8_12 : k + 1 + (j + 1) - 2 = k + j := by parley_ring
        -- 1.8.13. proof
        intro X hK6
        intro hC3
        -- 1.8.13.1. calculation
        have s1_8_13_1 : (LeanBridges.Counting.choose (k + j) k : ℤ) ≤ (X.ncard : ℤ) := by
          calc (LeanBridges.Counting.choose (k + j) k : ℤ) = (LeanBridges.Counting.choose (k + j) (k + 1 - 1) : ℤ) := by (have h := congrArg (fun t : ℤ => (LeanBridges.Counting.choose (k + j) t : ℤ)) s1_7.symm; push_cast at h ⊢; all_goals exact_mod_cast h)
            _ = (LeanBridges.Counting.choose (k + 1 + (j + 1) - 2) (k + 1 - 1) : ℤ) := by (have h := congrArg (fun t : ℤ => (LeanBridges.Counting.choose t (k + 1 - 1) : ℤ)) s1_8_12.symm; push_cast at h ⊢; all_goals exact_mod_cast h)
            _ ≤ (X.ncard : ℤ) := by parley_set_side
        -- 1.8.13.2. thm:ramsey-step, from H4, H7, K6, 1.8.8, 1.8.11, 1.8.13.1
        exact (Parley.Proofs.Wiedijk.Ramsey.RamseyStep.ramsey_step (V := V) (E := E) (F := F) (k := k) (lt_of_lt_of_le zero_lt_one hK3) (j := j) (lt_of_lt_of_le zero_lt_one hK5) hH4 hH7 (X := X) hK6 s1_8_13_1 s1_8_8 s1_8_11)
  -- 2. mun:subset-self
  have s2 : V ⊆ V := by exact (Parley.Items.Stdlib.Sets.mun_subset_self (X := V))
  -- 3. instantiate k := r, j := s, X := V in line 1, from H8, 2
  exact (s1 r hH1 s hH2 V s2 hH8)

end Parley.Proofs.Wiedijk.Ramsey.Ramsey
