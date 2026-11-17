module

public import Functions
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Data.ENat.Basic
public import Mathlib.Data.ENat.Defs
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Cast.Defs
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
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Set
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Sets
public import Parley.Proofs.Wiedijk.Subsets.AddElementBijection
public import Parley.Proofs.Wiedijk.Subsets.PowersetSplit
public import Parley.Proofs.Wiedijk.Subsets.PowersetSplitDisjoint

/-! Written from proofs/wiedijk/subsets.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.Subsets.SubsetsCount

theorem subsets_count {α : Type*} [Nonempty α] (A : Set α) (n : ℤ) (hH1 : 0 ≤ n) (hH3 : A.encard = ((n.toNat : ℕ) : ℕ∞)) :
    ((𝒫 A).ncard : ℤ) = 2 ^ n.toNat := by
  -- 1. induction on k starting at 0
  have s1 : ∀ k : ℤ, 0 ≤ k → (∀ X : Set γ, X.encard = ((k.toNat : ℕ) : ℕ∞) → ((𝒫 X).ncard : ℤ) = 2 ^ k.toNat) := by
    intro k h_k
    replace h_k : 0 ≤ k := by omega
    induction k, h_k using LeanBridges.Functions.le_induction with
    | base =>
      intro X
      intro hC1
      -- 1.1. mun:card-zero, from C1
      have s1_1 : X = ∅ := by exact (Parley.Items.Stdlib.Counting.mun_card_zero (X := X) (by simpa only [Int.reduceToNat, Nat.cast_zero] using hC1))
      -- 1.2. mun:card-singleton x := ∅
      have s1_2 : (({∅} : Set (Set α)).ncard : ℤ) = 1 := by exact (Parley.Items.Stdlib.Counting.mun_card_singleton (x := (∅ : Set α)))
      -- 1.3. calculation
      have s1_3 : 𝒫 X = ({∅} : Set (Set α)) := by
        calc 𝒫 X = 𝒫 (∅ : Set α) := congrArg (fun t : Set γ => 𝒫 t) s1_1
          _ = ({∅} : Set (Set α)) := by exact Parley.Items.Stdlib.Sets.mun_powerset_empty
      -- 1.4. substitute 𝒫X = {∅} (line 1.3) into line 1.2
      have s1_4 : ((𝒫 X).ncard : ℤ) = 1 := Eq.subst (motive := (fun t : Set (Set α) => (t.ncard : ℤ) = 1)) s1_3.symm s1_2
      -- 1.5. calculation
      have s1_5 : ((𝒫 X).ncard : ℤ) = 2 ^ 0 := by
        calc ((𝒫 X).ncard : ℤ) = 1 := s1_4
          _ = 2 ^ 0 := by norm_num
      simpa only [Int.reduceToNat, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Int.cast_ofNat, Int.cast_zero, Int.cast_one] using s1_5
    | succ k hK2 hIH =>
      intro X
      intro hC2
      -- 1.6. obtain a: mun:card-nonempty, from C2
      obtain ⟨a, s1_6, _⟩ := (Parley.Items.Stdlib.Counting.mun_card_nonempty (X := X) (k := k) hK2 (by rw [Set.ncard_def, hC2, ENat.toNat_coe, Int.toNat_of_nonneg (add_nonneg (hK2) (by norm_num))]))
      -- 1.7. mun:card-remove, from C2, 1.6
      have s1_7 : ((X \ ({a} : Set γ)).ncard : ℤ) = k := by exact (Parley.Items.Stdlib.Counting.mun_card_remove (X := X) (a := a) s1_6 (k := k) hK2 (by rw [Set.ncard_def, hC2, ENat.toNat_coe, Int.toNat_of_nonneg (add_nonneg (hK2) (by norm_num))]))
      set U : Set (Set γ) := 𝒫 (X \ ({a} : Set γ)) with hD1
      have hD1_finite : U.Finite := by rw [hD1]; exact ((Set.finite_of_encard_eq_coe hC2).subset (fun _ h => h.1)).powerset
      set T : Set (Set γ) := (fun S : Set γ => S ∪ ({a} : Set γ)) '' U with hD2
      have hD2_finite : T.Finite := by rw [hD2]; exact (hD1_finite).image _
      -- 1.8. instantiate X := X ∖ {a} in IH, from D1, 1.7
      have s1_8 : (U.ncard : ℤ) = 2 ^ k.toNat := by exact (hIH (X \ ({a} : Set γ)) (by (have h := congrArg Int.toNat (s1_7); rw [Int.toNat_natCast] at h; rw [← Set.Finite.cast_ncard_eq (((Set.finite_of_encard_eq_coe hC2).subset (fun _ h => h.1) : (X \ ({a} : Set γ) : Set γ).Finite)), h])))
      -- 1.9. thm:add-element-bijection X := X ∖ {a}, from D1, D2
      have r260_1 : ¬ a ∈ X \ ({a} : Set γ) := by exact (Parley.Items.Stdlib.Sets.mun_not_in_difference (X := X) (a := a))
      have s1_9 : ∃ g : Set γ → Set γ, Set.BijOn g U T := by
        simp only [hD1, hD2] at ⊢
        push_cast at ⊢
        exact (Parley.Proofs.Wiedijk.Subsets.AddElementBijection.add_element_bijection (X := X \ ({a} : Set γ)) (a := a) r260_1)
      -- 1.10. mun:card-bijection X := U, Y := T, m := 2^k, from 1.8, 1.9
      have s1_10 : (T.ncard : ℤ) = 2 ^ k.toNat := by rw [Set.ncard_def, (Parley.Items.Stdlib.Counting.mun_card_bijection (X := U) (Y := T) (m := (2 ^ k.toNat : ℤ)) (pow_nonneg (by norm_num) _) (by (have h := congrArg Int.toNat (s1_8); rw [Int.toNat_natCast] at h; rw [← Set.Finite.cast_ncard_eq ((hD1_finite : (U : Set (Set γ)).Finite)), h])) s1_9), ENat.toNat_coe, Int.toNat_of_nonneg (pow_nonneg (by norm_num) _)]
      -- 1.11. thm:powerset-split-disjoint, from D1, D2, 1.6
      have s1_11 : U ∩ T = ∅ := by
        simp only [hD1, hD2] at ⊢
        push_cast at ⊢
        exact (Parley.Proofs.Wiedijk.Subsets.PowersetSplitDisjoint.powerset_split_disjoint (X := X) (a := a) s1_6)
      -- 1.12. thm:powerset-split, from D1, D2, 1.6
      have s1_12 : 𝒫 X = U ∪ T := by
        simp only [hD1, hD2] at ⊢
        push_cast at ⊢
        exact (Parley.Proofs.Wiedijk.Subsets.PowersetSplit.powerset_split (X := X) (a := a) s1_6)
      -- 1.13. mun:card-disjoint-union X := U, Y := T, m := 2^k, n := 2^k, from 1.8, 1.10, 1.11
      have s1_13 : ((U ∪ T).ncard : ℤ) = 2 ^ k.toNat + 2 ^ k.toNat := by exact (Parley.Items.Stdlib.Counting.mun_card_disjoint_union (X := U) (Y := T) (m := (2 ^ k.toNat : ℤ)) (pow_nonneg (by norm_num) _) (n := (2 ^ k.toNat : ℤ)) (pow_nonneg (by norm_num) _) (by (have h := congrArg Int.toNat (s1_8); rw [Int.toNat_natCast] at h; rw [← Set.Finite.cast_ncard_eq ((hD1_finite : (U : Set (Set γ)).Finite)), h])) (by (have h := congrArg Int.toNat (s1_10); rw [Int.toNat_natCast] at h; rw [← Set.Finite.cast_ncard_eq ((hD2_finite : (T : Set (Set γ)).Finite)), h])) s1_11)
      -- 1.14. substitute 𝒫X = U ∪ T (line 1.12) into line 1.13
      have s1_14 : ((𝒫 X).ncard : ℤ) = 2 ^ k.toNat + 2 ^ k.toNat := Eq.subst (motive := (fun t : Set (Set γ) => (t.ncard : ℤ) = 2 ^ k.toNat + 2 ^ k.toNat)) s1_12.symm s1_13
      -- 1.15. calculation
      calc ((𝒫 X).ncard : ℤ) = 2 ^ k.toNat + 2 ^ k.toNat := s1_14
        _ = 2 ^ k.toNat * 2 := by ring1
        _ = 2 ^ (k + 1).toNat := by exact (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k) hK2).symm
  -- 2. instantiate k := n, X := A in line 1, from H2, H3
  exact (s1 n hH1 A hH3)

end Parley.Proofs.Wiedijk.Subsets.SubsetsCount
