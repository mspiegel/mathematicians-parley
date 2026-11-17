module

public import Counting
public import Functions
public import Batteries.Util.ExtendedBinder
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Data.ENat.Basic
public import Mathlib.Data.ENat.Defs
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Cast.Order.Ring
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Set
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Sets
public import Parley.Proofs.Wiedijk.Combinations.AddElementBijection
public import Parley.Proofs.Wiedijk.Combinations.AddElementDisjoint
public import Parley.Proofs.Wiedijk.Combinations.ChooseFromNone
public import Parley.Proofs.Wiedijk.Combinations.ChooseSplit

/-! Written from proofs/wiedijk/combinations.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.Combinations.Combinations

theorem combinations {α : Type*} [Nonempty α] (A : Set α) (n : ℤ) (hH1 : 0 ≤ n) (k : ℤ) (hH4 : A.encard = ((n.toNat : ℕ) : ℕ∞)) :
    ({S ∈ 𝒫 A | (S.ncard : ℤ) = k}.ncard : ℤ) = (LeanBridges.Counting.choose n k : ℤ) := by
  -- 1. induction on m starting at 0
  have s1 : ∀ m : ℤ, 0 ≤ m → (∀ X : Set α, ∀ j : ℤ, X.encard = ((m.toNat : ℕ) : ℕ∞) → ({S ∈ 𝒫 X | (S.ncard : ℤ) = j}.ncard : ℤ) = (LeanBridges.Counting.choose m j : ℤ)) := by
    intro m h_m
    replace h_m : 0 ≤ m := by omega
    induction m, h_m using LeanBridges.Functions.le_induction with
    | base =>
      intro X
      intro j
      intro hC1
      -- 1.1. thm:choose-from-none, from C1
      exact (Parley.Proofs.Wiedijk.Combinations.ChooseFromNone.choose_from_none (X := X) (j := j) (by simpa only [Int.reduceToNat, Nat.cast_zero] using hC1))
    | succ m hK3 hIH =>
      intro X
      intro j
      intro hC2
      -- 1.2. obtain a: mun:card-nonempty, from C2
      obtain ⟨a, s1_2, _⟩ := (Parley.Items.Stdlib.Counting.mun_card_nonempty (X := X) (k := m) hK3 (by rw [Set.ncard_def, hC2, ENat.toNat_coe, Int.toNat_of_nonneg (add_nonneg (hK3) (by norm_num))]))
      -- 1.3. mun:card-remove, from C2, 1.2
      have s1_3 : ((X \ ({a} : Set α)).ncard : ℤ) = m := by exact (Parley.Items.Stdlib.Counting.mun_card_remove (X := X) (a := a) s1_2 (k := m) hK3 (by rw [Set.ncard_def, hC2, ENat.toNat_coe, Int.toNat_of_nonneg (add_nonneg (hK3) (by norm_num))]))
      -- 1.4. mun:card-finite m := m + 1, from C2
      have s1_4 : X.Finite := by exact (Parley.Items.Stdlib.Counting.mun_card_finite (X := X) (m := m + 1) (add_nonneg (hK3) (by norm_num)) hC2)
      set U : Set (Set α) := {S ∈ 𝒫 (X \ ({a} : Set α)) | (S.ncard : ℤ) = j} with hD1
      have hD1_finite : U.Finite := by rw [hD1]; exact (((s1_4).subset (fun _ h => h.1)).powerset).subset (fun _ h => h.1)
      set V : Set (Set α) := {S ∈ 𝒫 (X \ ({a} : Set α)) | (S.ncard : ℤ) = j - 1} with hD2
      have hD2_finite : V.Finite := by rw [hD2]; exact (((s1_4).subset (fun _ h => h.1)).powerset).subset (fun _ h => h.1)
      set W : Set (Set α) := (fun T : Set α => T ∪ ({a} : Set α)) '' V with hD3
      have hD3_finite : W.Finite := by rw [hD3]; exact (hD2_finite).image _
      -- 1.5. instantiate X := X ∖ {a}, j := j in IH, from D1, 1.3
      have s1_5 : (U.ncard : ℤ) = (LeanBridges.Counting.choose m j : ℤ) := by exact (hIH (X \ ({a} : Set α)) j (by (have h := congrArg Int.toNat (s1_3); rw [Int.toNat_natCast] at h; rw [← Set.Finite.cast_ncard_eq (((s1_4).subset (fun _ h => h.1) : (X \ ({a} : Set α) : Set α).Finite)), h])))
      -- 1.6. instantiate X := X ∖ {a}, j := j − 1 in IH, from D2, 1.3
      have s1_6 : (V.ncard : ℤ) = (LeanBridges.Counting.choose m (j - 1) : ℤ) := by exact (hIH (X \ ({a} : Set α)) (j - 1) (by (have h := congrArg Int.toNat (s1_3); rw [Int.toNat_natCast] at h; rw [← Set.Finite.cast_ncard_eq (((s1_4).subset (fun _ h => h.1) : (X \ ({a} : Set α) : Set α).Finite)), h])))
      -- 1.7. thm:add-element-bijection Y := X ∖ {a}, j := j − 1, from D2, D3
      have r463_1 : ¬ a ∈ X \ ({a} : Set α) := by exact (Parley.Items.Stdlib.Sets.mun_not_in_difference (X := X) (a := a))
      have s1_7 : ∃ g : Set α → Set α, Set.BijOn g V W := by
        simp only [hD2, hD3] at ⊢
        push_cast at ⊢
        (have h := (Parley.Proofs.Wiedijk.Combinations.AddElementBijection.add_element_bijection (Y := X \ ({a} : Set α)) (a := a) r463_1 (j := j - 1)); simp only [LeanBridges.Counting.builder_count_spelt (X \ ({a} : Set α)) ((s1_4).subset (fun _ h => h.1))] at h ⊢; exact h)
      -- 1.8. mun:card-bijection X := V, Y := W, m := C(m, j − 1), from 1.6, 1.7
      have s1_8 : (W.ncard : ℤ) = (LeanBridges.Counting.choose m (j - 1) : ℤ) := by rw [Set.ncard_def, (Parley.Items.Stdlib.Counting.mun_card_bijection (X := V) (Y := W) (m := (LeanBridges.Counting.choose m (j - 1) : ℤ)) (Nat.cast_nonneg _) (by (have h := congrArg Int.toNat (s1_6); rw [Int.toNat_natCast] at h; rw [← Set.Finite.cast_ncard_eq ((hD2_finite : (V : Set (Set α)).Finite)), h])) s1_7), ENat.toNat_coe, Int.toNat_of_nonneg (Nat.cast_nonneg _)]
      -- 1.9. thm:add-element-disjoint Y := X ∖ {a}, from D1, D2, D3
      have r471_1 : ¬ a ∈ X \ ({a} : Set α) := by exact (Parley.Items.Stdlib.Sets.mun_not_in_difference (X := X) (a := a))
      have s1_9 : U ∩ W = ∅ := by
        simp only [hD1, hD2, hD3] at ⊢
        push_cast at ⊢
        (have h := (Parley.Proofs.Wiedijk.Combinations.AddElementDisjoint.add_element_disjoint (Y := X \ ({a} : Set α)) (a := a) r471_1 (j := j)); simp only [LeanBridges.Counting.builder_count_spelt (X \ ({a} : Set α)) ((s1_4).subset (fun _ h => h.1))] at h ⊢; exact h)
      -- 1.10. thm:choose-split, from D1, D2, D3, 1.2, 1.4
      have s1_10 : {S ∈ 𝒫 X | (S.ncard : ℤ) = j} = U ∪ W := by
        simp only [hD1, hD2, hD3] at ⊢
        push_cast at ⊢
        exact (Parley.Proofs.Wiedijk.Combinations.ChooseSplit.choose_split (X := X) (a := a) s1_2 (j := j) s1_4)
      -- 1.11. mun:card-disjoint-union X := U, Y := W, m := C(m, j), n := C(m, j − 1), from 1.5, 1.8, 1.9
      have s1_11 : ((U ∪ W).ncard : ℤ) = (LeanBridges.Counting.choose m j : ℤ) + (LeanBridges.Counting.choose m (j - 1) : ℤ) := by exact (Parley.Items.Stdlib.Counting.mun_card_disjoint_union (X := U) (Y := W) (m := (LeanBridges.Counting.choose m j : ℤ)) (Nat.cast_nonneg _) (n := (LeanBridges.Counting.choose m (j - 1) : ℤ)) (Nat.cast_nonneg _) (by (have h := congrArg Int.toNat (s1_5); rw [Int.toNat_natCast] at h; rw [← Set.Finite.cast_ncard_eq ((hD1_finite : (U : Set (Set α)).Finite)), h])) (by (have h := congrArg Int.toNat (s1_8); rw [Int.toNat_natCast] at h; rw [← Set.Finite.cast_ncard_eq ((hD3_finite : (W : Set (Set α)).Finite)), h])) s1_9)
      -- 1.12. substitute {S ⊆ X : |S| = j} = U ∪ W (line 1.10) into line 1.11
      have s1_12 : ({S ∈ 𝒫 X | (S.ncard : ℤ) = j}.ncard : ℤ) = (LeanBridges.Counting.choose m j : ℤ) + (LeanBridges.Counting.choose m (j - 1) : ℤ) := Eq.subst (motive := (fun t : Set (Set α) => (t.ncard : ℤ) = (LeanBridges.Counting.choose m j : ℤ) + (LeanBridges.Counting.choose m (j - 1) : ℤ))) s1_10.symm s1_11
      -- 1.13. calculation
      calc ({S ∈ 𝒫 X | (S.ncard : ℤ) = j}.ncard : ℤ) = (LeanBridges.Counting.choose m j : ℤ) + (LeanBridges.Counting.choose m (j - 1) : ℤ) := s1_12
        _ = (LeanBridges.Counting.choose (m + 1) j : ℤ) := by exact (Parley.Items.Stdlib.Counting.thm_pascal (n := m) hK3 (k := j))
  -- 2. instantiate m := n, X := A, j := k in line 1, from H3, H4
  exact (s1 n hH1 A k hH4)

end Parley.Proofs.Wiedijk.Combinations.Combinations
