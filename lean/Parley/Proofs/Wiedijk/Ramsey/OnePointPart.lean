module

public import SetTactics
public import Tactics
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Proofs.Wiedijk.Ramsey
public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/wiedijk/ramsey.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.Ramsey.OnePointPart

theorem one_point_part {α : Type*} (X : Set α) (G : Set (Set α)) (hH2 : X.Finite) (hH3 : 1 ≤ (X.ncard : ℤ)) :
    (∃ W ∈ 𝒫 X, 1 ≤ (W.ncard : ℤ) ∧ (∀ Y ∈ 𝒫 W, (Y.ncard : ℤ) = 2 → Y ∈ G)) := by
  -- 1. inequalities, from H3
  have r61_1 : 0 ≤ (X.ncard : ℤ) := by exact (Parley.Items.Stdlib.Counting.mun_card_nat0 (X := X) hH2)
  have s1 : 0 < (X.ncard : ℤ) := by parley_count_int; (linarith only [hH3])
  -- 2. mun:card-positive, from 1
  have s2 : ¬ X = ∅ := by exact (Parley.Items.Stdlib.Counting.mun_card_positive (X := X) (by (have h := s1; rw [← Set.Finite.cast_ncard_eq ((hH2 : (X : Set α).Finite))]; norm_cast at h ⊢; all_goals omega)))
  -- 3. obtain v: mun:nonempty-member, from 2
  obtain ⟨v, s3, _⟩ := (Parley.Items.Stdlib.Sets.mun_nonempty_member (Y := X) s2)
  -- 4. mun:singleton-subset, from 3
  have s4 : ({v} : Set α) ⊆ X := by exact (Parley.Items.Stdlib.Sets.mun_singleton_subset (X := X) (a := v) s3)
  -- 5. mun:card-singleton x := v
  have s5 : (({v} : Set α).ncard : ℤ) = 1 := by exact (Parley.Items.Stdlib.Counting.mun_card_singleton (x := v))
  -- 6. proof
  have s6 : ∀ Y ∈ 𝒫 ({v} : Set α), (Y.ncard : ℤ) = 2 → Y ∈ G := by
    intro Y hK1
    intro hK2
    -- 6.1. mun:card-subset A := Y, B := {v}, from K1
    have s6_1 : (Y.ncard : ℤ) ≤ (({v} : Set α).ncard : ℤ) := by (have h := (Parley.Items.Stdlib.Counting.mun_card_subset (A := Y) (B := ({v} : Set α)) hK1); simp only [← Set.Finite.cast_ncard_eq ((Set.finite_of_ncard_ne_zero (by omega) : (Y : Set α).Finite)), ← Set.Finite.cast_ncard_eq ((Set.finite_of_ncard_ne_zero (by omega) : (({v} : Set α) : Set α).Finite))] at h ⊢; exact_mod_cast h)
    -- 6.2. substitute |{v}| = 1 (line 5) into line 6.1
    have s6_2 : (Y.ncard : ℤ) ≤ 1 := by (have h := Eq.subst (motive := (fun t : ℤ => (Y.ncard : ℤ) ≤ t)) s5 s6_1; push_cast at h ⊢; all_goals exact_mod_cast h)
    -- 6.3. substitute |Y| = 2 (K2) into line 6.2
    have s6_3 : (2 : ℤ) ≤ 1 := by (have h := Eq.subst (motive := (fun t : ℤ => t ≤ 1)) hK2 s6_2; push_cast at h ⊢; all_goals exact_mod_cast h)
    exact absurd s6_3 (by norm_num)
  -- 7. inequalities
  have s7 : 1 ≤ (({v} : Set α).ncard : ℤ) := by parley_count_int; (linarith only [s5])
  -- 8. D1, from 6, 7
  have s8 : 1 ≤ (({v} : Set α).ncard : ℤ) ∧ (∀ Y ∈ 𝒫 ({v} : Set α), (Y.ncard : ℤ) = 2 → Y ∈ G) := ⟨s7, s6⟩
  -- 9. exhibit, from 4, 8
  exact ⟨({v} : Set α), s4, s8⟩

end Parley.Proofs.Wiedijk.Ramsey.OnePointPart
