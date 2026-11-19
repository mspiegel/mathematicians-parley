module

public import Counting
public import Batteries.Util.ExtendedBinder
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Interval.Set.Defs
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
public import Mathlib.Tactic.SetNotationForOrder
public import Parley.Items.Proofs.Wiedijk.Ballot
public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Sets
public import Parley.Items.Stdlib.Sums
public import Parley.Proofs.Wiedijk.Ballot.LastPlace
public import Parley.Proofs.Wiedijk.Combinations.Combinations

/-! Written from proofs/wiedijk/ballot.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.Ballot.NoVotesForB

theorem no_votes_for_b (m : ℤ) (hH1 : 0 < m) :
    ({c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m + 0) : Set ℤ) | (d.ncard : ℤ) = m} | ∀ i : ℤ, i ∈ Finset.Icc 1 (m + 0) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)}.ncard : ℤ) = 1 := by
  set O : Set (Set ℤ) := {d ∈ 𝒫 (Set.Icc (1 : ℤ) m : Set ℤ) | (d.ncard : ℤ) = m} with hD3
  have hD3_finite : O.Finite := by rw [hD3]; exact ((Set.finite_Icc _ _).powerset).subset (fun _ h => h.1)
  -- 1. proof
  have s1 : ∀ c ∈ O, c ∈ {c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m + 0) : Set ℤ) | (d.ncard : ℤ) = m} | ∀ i : ℤ, i ∈ Finset.Icc 1 (m + 0) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)} := by
    intro c hK1
    -- 1.1. def:part-builder u := c, from D3, K1
    have s1_1a : c ⊆ (Set.Icc (1 : ℤ) m : Set ℤ) := by exact (((Parley.Items.Stdlib.Sets.def_part_builder (P := (fun d : Set ℤ => (d.ncard : ℤ) = m)) (X := (Set.Icc (1 : ℤ) m : Set ℤ)) (u := c))).mp hK1).1
    have s1_1b : (c.ncard : ℤ) = m := by
      have hI : (c.ncard : ℤ) = m := by exact ((((Parley.Items.Stdlib.Sets.def_part_builder (P := (fun d : Set ℤ => (d.ncard : ℤ) = m)) (X := (Set.Icc (1 : ℤ) m : Set ℤ)) (u := c))).mp hK1).2)
      exact hI
    -- 1.2. thm:last-place n := 0, from 1.1
    have s1_2 : (((Set.Icc (1 : ℤ) m : Set ℤ) \ c).ncard : ℤ) = 0 := by simpa only [Int.cast_one, add_zero] using (Parley.Proofs.Wiedijk.Ballot.LastPlace.last_place (m := m) (le_of_lt hH1) (n := (0 : ℤ)) (by norm_num) (c := c) (by simpa only [Int.cast_one, Int.cast_zero, add_zero] using s1_1a) s1_1b).1
    -- 1.3. mun:card-zero X := {1, …, m} ∖ c, from 1.2
    have s1_3 : (Set.Icc (1 : ℤ) m : Set ℤ) \ c = ∅ := by exact (Parley.Items.Stdlib.Counting.mun_card_zero (X := (Set.Icc (1 : ℤ) m : Set ℤ) \ c) (by (have h := s1_2; rw [← Set.Finite.cast_ncard_eq (((Set.finite_Icc _ _).subset (fun _ h => h.1) : ((Set.Icc (1 : ℤ) m : Set ℤ) \ c : Set ℤ).Finite))]; exact_mod_cast h)))
    -- 1.4. mun:nothing-left-outside Y := {1, …, m}, X := c, from 1.3
    have s1_4 : (Set.Icc (1 : ℤ) m : Set ℤ) ⊆ c := ((Parley.Items.Stdlib.Sets.mun_nothing_left_outside (X := c) (Y := (Set.Icc (1 : ℤ) m : Set ℤ)))).mpr s1_3
    -- 1.5. proof
    have s1_5 : ∀ i : ℤ, i ∈ Finset.Icc 1 m → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ) := by
      intro i hK2
      have hK2_bounds := Finset.mem_Icc.mp hK2
      -- 1.5.1. mun:range-bounds a := 1, b := m, k := i, from K2
      have s1_5_1a : 1 ≤ i := by exact (Parley.Items.Stdlib.Sums.mun_range_bounds_1 (a := (1 : ℤ)) (b := m) (k := i) hK2)
      have s1_5_1b : i ≤ m := by exact (Parley.Items.Stdlib.Sums.mun_range_bounds_2 (a := (1 : ℤ)) (b := m) (k := i) hK2)
      -- 1.5.2. mun:range-within a := 1, k := i, n := m, from 1.5.1
      have s1_5_2 : (Set.Icc (1 : ℤ) i : Set ℤ) ⊆ (Set.Icc (1 : ℤ) m : Set ℤ) := by exact (Parley.Items.Stdlib.Sums.mun_range_within (a := (1 : ℤ)) (k := i) (n := m) s1_5_1b)
      -- 1.5.3. mun:nothing-left-outside Y := {1, …, i}, X := {1, …, m}, from 1.5.2
      have s1_5_3 : (Set.Icc (1 : ℤ) i : Set ℤ) \ (Set.Icc (1 : ℤ) m : Set ℤ) = ∅ := by exact ((Parley.Items.Stdlib.Sets.mun_nothing_left_outside (X := (Set.Icc (1 : ℤ) m : Set ℤ)) (Y := (Set.Icc (1 : ℤ) i : Set ℤ)))).mp s1_5_2
      -- 1.5.4. calculation
      have s1_5_4 : (Set.Icc (1 : ℤ) i : Set ℤ) ∩ (Set.Icc (1 : ℤ) m : Set ℤ) = (Set.Icc (1 : ℤ) i : Set ℤ) := by
        calc (Set.Icc (1 : ℤ) i : Set ℤ) ∩ (Set.Icc (1 : ℤ) m : Set ℤ) = (Set.Icc (1 : ℤ) m : Set ℤ) ∩ (Set.Icc (1 : ℤ) i : Set ℤ) := by exact (Parley.Items.Stdlib.Sets.mun_intersection_commutes (Y := (Set.Icc (1 : ℤ) i : Set ℤ)) (Z := (Set.Icc (1 : ℤ) m : Set ℤ)))
          _ = (Set.Icc (1 : ℤ) i : Set ℤ) := by exact (Parley.Items.Stdlib.Sets.mun_intersection_of_part (X := (Set.Icc (1 : ℤ) m : Set ℤ)) (Y := (Set.Icc (1 : ℤ) i : Set ℤ)) s1_5_2)
      -- 1.5.5. inequalities, from 1.5.1
      have s1_5_5 : 0 < i := by linarith only [s1_5_1a]
      -- 1.5.6. calculation
      have s1_5_6 : (((Set.Icc (1 : ℤ) i : Set ℤ) \ (Set.Icc (1 : ℤ) m : Set ℤ)).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ (Set.Icc (1 : ℤ) m : Set ℤ)).ncard : ℤ) := by
        calc (((Set.Icc (1 : ℤ) i : Set ℤ) \ (Set.Icc (1 : ℤ) m : Set ℤ)).ncard : ℤ) = ((∅ : Set ℤ).ncard : ℤ) := congrArg (fun t : Set ℤ => (t.ncard : ℤ)) s1_5_3
          _ = 0 := by exact Parley.Items.Stdlib.Counting.mun_card_empty
          _ < i := s1_5_5
          _ = ((Set.Icc (1 : ℤ) i : Set ℤ).ncard : ℤ) := by exact (Parley.Items.Stdlib.Counting.mun_range_size (n := i) (le_trans (by norm_num) (Finset.mem_Icc.mp hK2).1)).symm
          _ = (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ (Set.Icc (1 : ℤ) m : Set ℤ)).ncard : ℤ) := congrArg (fun t : Set ℤ => (t.ncard : ℤ)) s1_5_4.symm
      -- 1.5.7. substitute
      have c1 : (Set.Icc (1 : ℤ) m : Set ℤ) = c := by exact (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := c) (Y := (Set.Icc (1 : ℤ) m : Set ℤ)) s1_1a s1_4).symm
      have row1 : (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ) := Eq.subst (motive := (fun t : Set ℤ => (((Set.Icc (1 : ℤ) i : Set ℤ) \ t).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ t).ncard : ℤ))) c1 s1_5_6
      exact row1
    -- 1.6. D1, from 1.5
    have s1_6 : ∀ i : ℤ, i ∈ Finset.Icc 1 m → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ) := s1_5
    -- 1.7. def:set-builder u := c, from D2, D3, K1, 1.6
    exact ((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun c : Set ℤ => ∀ i : ℤ, i ∈ Finset.Icc 1 (m + 0) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ))) (X := {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m + 0) : Set ℤ) | (d.ncard : ℤ) = m}) (u := c))).mpr ⟨by simpa only [Int.cast_one, add_zero] using hK1, by simpa only [Int.cast_one, add_zero] using s1_6⟩
  -- 2. def:subset, from 1
  have s2 : O ⊆ {c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m + 0) : Set ℤ) | (d.ncard : ℤ) = m} | ∀ i : ℤ, i ∈ Finset.Icc 1 (m + 0) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)} := ((Parley.Items.Stdlib.Sets.def_subset (X := O) (Y := {c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m + 0) : Set ℤ) | (d.ncard : ℤ) = m} | ∀ i : ℤ, i ∈ Finset.Icc 1 (m + 0) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)}))).mpr s1
  -- 3. mun:set-builder-subset X := O, from D2, D3
  have s3 : {c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m + 0) : Set ℤ) | (d.ncard : ℤ) = m} | ∀ i : ℤ, i ∈ Finset.Icc 1 (m + 0) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)} ⊆ O := by
    simp only [hD3] at ⊢
    push_cast at ⊢
    have hI : {t ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) m : Set ℤ) | (d.ncard : ℤ) = m} | ∀ a : ℤ, a ∈ Finset.Icc 1 (m + 0) → (((Set.Icc (1 : ℤ) a : Set ℤ) \ t).ncard : ℤ) < (((Set.Icc (1 : ℤ) a : Set ℤ) ∩ t).ncard : ℤ)} ⊆ {d ∈ 𝒫 (Set.Icc (1 : ℤ) m : Set ℤ) | (d.ncard : ℤ) = m} := by exact ((Parley.Items.Stdlib.Sets.mun_set_builder_subset (P := (fun c : Set ℤ => ∀ i : ℤ, i ∈ Finset.Icc 1 (m + 0) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ))) (X := {d ∈ 𝒫 (Set.Icc (1 : ℤ) m : Set ℤ) | (d.ncard : ℤ) = m})))
    simpa only [Int.cast_one, add_zero] using hI
  -- 4. mun:subset-antisymmetric, from 2, 3
  have s4 : {c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m + 0) : Set ℤ) | (d.ncard : ℤ) = m} | ∀ i : ℤ, i ∈ Finset.Icc 1 (m + 0) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)} = O := by exact (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := {c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m + 0) : Set ℤ) | (d.ncard : ℤ) = m} | ∀ i : ℤ, i ∈ Finset.Icc 1 (m + 0) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)}) (Y := O) s3 s2)
  -- 5. mun:range-size n := m
  have s5 : ((Set.Icc (1 : ℤ) m : Set ℤ).ncard : ℤ) = m := by exact (Parley.Items.Stdlib.Counting.mun_range_size (n := m) (le_of_lt hH1))
  -- 6. calculation
  calc ({c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m + 0) : Set ℤ) | (d.ncard : ℤ) = m} | ∀ i : ℤ, i ∈ Finset.Icc 1 (m + 0) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)}.ncard : ℤ) = (O.ncard : ℤ) := congrArg (fun t : Set (Set ℤ) => (t.ncard : ℤ)) s4
    _ = (LeanBridges.Counting.choose m m : ℤ) := by
        simp only [hD3] at ⊢
        push_cast at ⊢
        (have h := (Parley.Proofs.Wiedijk.Combinations.Combinations.combinations (A := (Set.Icc (1 : ℤ) m : Set ℤ)) (n := m) (le_of_lt hH1) (k := m) (by (have h := congrArg Int.toNat (s5); rw [Int.toNat_natCast] at h; rw [← Set.Finite.cast_ncard_eq ((Set.finite_of_ncard_ne_zero (fun h0 => by have h := s5; rw [h0] at h; exact ne_of_lt ((hH1 : 0 < m)) (by exact_mod_cast h)) : ((Set.Icc (1 : ℤ) m : Set ℤ) : Set ℤ).Finite)), h]))); push_cast at h; exact h)
    _ = 1 := by exact (Parley.Items.Stdlib.Counting.mun_binomial_all (n := m) (le_of_lt hH1))

end Parley.Proofs.Wiedijk.Ballot.NoVotesForB
