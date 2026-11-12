module

public import Counting
public import FactorialTactics
public import SetTactics
public import SubstTactics
public import Tactics
public import Batteries.Util.ExtendedBinder
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Data.ENat.Defs
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Set
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Reasoning
public import Parley.Items.Stdlib.Sets
public import Parley.Items.Stdlib.Sums

/-! Written from proofs/wiedijk/combinations.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.Combinations.ChooseFromNone

theorem choose_from_none {α : Type*} (X : Set α) (j : ℤ) (hH3 : X.encard = ((0 : ℕ) : ℕ∞)) :
    ({S ∈ 𝒫 X | (S.ncard : ℤ) = j}.ncard : ℤ) = (LeanBridges.Counting.choose (0 : ℤ) j : ℤ) := by
  set F : Set (Set α) := {S ∈ 𝒫 X | (S.ncard : ℤ) = j} with hD1
  have hD1_finite : F.Finite := by rw [hD1]; exact ((Set.finite_of_encard_eq_coe hH3).powerset).subset (fun _ h => h.1)
  -- 1. mun:card-zero, from H3
  have s1 : X = ∅ := by exact (Parley.Items.Stdlib.Counting.mun_card_zero (X := X) (by parley_set_side))
  -- 2. axi:excluded-middle P := j = 0
  have s2 : j = 0 ∨ j ≠ 0 := by exact (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := j = 0))
  -- 3. cases, from 2
  have s3 : (F.ncard : ℤ) = (LeanBridges.Counting.choose (0 : ℤ) j : ℤ) := by
    rcases s2 with hC1 | hC2
    · skip
      -- 3.1. mun:empty-subset
      have s3_1 : ∅ ⊆ X := by exact (Parley.Items.Stdlib.Sets.mun_empty_subset (X := X))
      -- 3.2. calculation
      have s3_2 : ((∅ : Set α).ncard : ℤ) = j := by
        calc ((∅ : Set α).ncard : ℤ) = 0 := by exact Parley.Items.Stdlib.Counting.mun_card_empty
          _ = j := by parley_set_side
      -- 3.3. def:part-builder u := ∅, from D1, 3.1, 3.2
      have s3_3 : ∅ ∈ F := ((Parley.Items.Stdlib.Sets.def_part_builder (P := (fun S : Set α => (S.ncard : ℤ) = j)) (X := X) (u := ∅))).mpr ⟨s3_1, by parley_set_side⟩
      -- 3.4. proof
      have s3_4 : ∀ R ∈ F, R ∈ ({∅} : Set (Set α)) := by
        intro R hK1
        -- 3.4.1. def:part-builder u := R, from D1, K1
        have s3_4_1 : R ⊆ X := by
          try simp only [hD1] at ⊢
          try push_cast at ⊢
          exact (((Parley.Items.Stdlib.Sets.def_part_builder (P := (fun S : Set α => (S.ncard : ℤ) = j)) (X := X) (u := R))).mp (by parley_set_side)).1
        -- 3.4.2. substitute X = ∅ (line 1) into line 3.4.1
        have s3_4_2 : R ⊆ ∅ := by parley_subst_at s1 s3_4_1
        -- 3.4.3. mun:subset-empty, from 3.4.2
        have s3_4_3 : R = ∅ := by exact ((Parley.Items.Stdlib.Sets.mun_subset_empty (Y := R))).mp s3_4_2
        -- 3.4.4. def:singleton x := R, a := ∅, from 3.4.3
        exact ((Parley.Items.Stdlib.Sets.def_singleton (a := (∅ : Set α)) (x := R))).mpr s3_4_3
      -- 3.5. def:subset, from 3.4
      have s3_5 : F ⊆ ({∅} : Set (Set α)) := ((Parley.Items.Stdlib.Sets.def_subset (X := F) (Y := ({∅} : Set (Set α))))).mpr s3_4
      -- 3.6. mun:singleton-subset, from 3.3
      have s3_6 : ({∅} : Set (Set α)) ⊆ F := by exact (Parley.Items.Stdlib.Sets.mun_singleton_subset (X := F) (a := (∅ : Set α)) (by parley_set_side))
      -- 3.7. mun:subset-antisymmetric, from 3.5, 3.6
      have s3_7 : F = ({∅} : Set (Set α)) := by exact (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := F) (Y := ({∅} : Set (Set α))) s3_5 s3_6)
      -- 3.8. calculation
      calc (F.ncard : ℤ) = (({∅} : Set (Set α)).ncard : ℤ) := by parley_subst s3_7
        _ = 1 := by exact (Parley.Items.Stdlib.Counting.mun_card_singleton (x := (∅ : Set α)))
        _ = (LeanBridges.Counting.choose (0 : ℤ) (0 : ℤ) : ℤ) := by exact (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := (0 : ℤ)) (by parley_set_side)).symm
        _ = (LeanBridges.Counting.choose (0 : ℤ) j : ℤ) := by (have h := congrArg (fun t : ℤ => (LeanBridges.Counting.choose (0 : ℤ) t : ℤ)) hC1.symm; push_cast at h ⊢; all_goals exact_mod_cast h)
    · skip
      -- 3.9. proof
      have s3_9 : ∀ R ∈ 𝒫 X, (R.ncard : ℤ) ≠ j := by
        intro R hK2
        intro hS1
        -- 3.9.1. substitute X = ∅ (line 1) into K2
        have s3_9_1 : R ⊆ ∅ := by parley_subst_at s1 hK2
        -- 3.9.2. mun:subset-empty, from 3.9.1
        have s3_9_2 : R = ∅ := by exact ((Parley.Items.Stdlib.Sets.mun_subset_empty (Y := R))).mp s3_9_1
        -- 3.9.3. calculation
        have s3_9_3 : j = 0 := by
          calc j = (R.ncard : ℤ) := by parley_set_side
            _ = ((∅ : Set α).ncard : ℤ) := by parley_subst s3_9_2
            _ = 0 := by exact Parley.Items.Stdlib.Counting.mun_card_empty
        -- 3.9.4. restate C2
        have s3_9_4 : j ≠ 0 := by exact hC2
        exact s3_9_4 s3_9_3
      -- 3.10. mun:part-builder-empty, from D1, 3.9
      have s3_10 : F = ∅ := ((Parley.Items.Stdlib.Sets.mun_part_builder_empty (P := (fun S : Set α => (S.ncard : ℤ) = j)) (X := X))).mpr (by parley_set_side)
      -- 3.11. contradiction
      have s3_11 : ¬ j ∈ Finset.Icc (0 : ℤ) (0 : ℤ) := by
        intro hS2
        -- 3.11.1. mun:range-bounds a := 0, b := 0, k := j, from S2
        have s3_11_1 : j ≤ 0 := by exact (Parley.Items.Stdlib.Sums.mun_range_bounds_2 (a := (0 : ℤ)) (b := (0 : ℤ)) (k := j) hS2)
        -- 3.11.2. mun:range-bounds a := 0, b := 0, k := j, from S2
        have s3_11_2 : 0 ≤ j := by exact (Parley.Items.Stdlib.Sums.mun_range_bounds_1 (a := (0 : ℤ)) (b := (0 : ℤ)) (k := j) hS2)
        -- 3.11.3. antisymmetry, from 3.11.1, 3.11.2
        have s3_11_3 : j = 0 := le_antisymm s3_11_1 s3_11_2
        -- 3.11.4. restate C2
        have s3_11_4 : j ≠ 0 := by exact hC2
        exact s3_11_4 s3_11_3
      -- 3.12. calculation
      calc (F.ncard : ℤ) = ((∅ : Set (Set α)).ncard : ℤ) := by parley_subst s3_10
        _ = 0 := by exact Parley.Items.Stdlib.Counting.mun_card_empty
        _ = (LeanBridges.Counting.choose (0 : ℤ) j : ℤ) := by exact (Parley.Items.Stdlib.Counting.mun_binomial_outside (n := (0 : ℤ)) (by parley_set_side) (k := j) s3_11).symm
  -- 4. substitute F = {S ⊆ X : |S| = j} (D1) into line 3
  parley_subst_at hD1 s3

end Parley.Proofs.Wiedijk.Combinations.ChooseFromNone
