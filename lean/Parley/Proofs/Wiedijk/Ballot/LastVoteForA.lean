module

public import AlgebraTactics
public import InstanceTactics
public import NormTactics
public import OrderTactics
public import SetTactics
public import SubstTactics
public import Tactics
public import WholeTactics
public import Batteries.Util.ExtendedBinder
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Set
public import Mathlib.Tactic.SetNotationForOrder
public import Parley.Items.Proofs.Wiedijk.Ballot
public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Functions
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Sets
public import Parley.Items.Stdlib.Sums
public import Parley.Proofs.Wiedijk.Ballot.LeadToTheEnd
public import Parley.Proofs.Wiedijk.Ballot.PlacesBeforeLast
public import Parley.Proofs.Wiedijk.Ballot.PrefixUnchanged

/-! Written from proofs/wiedijk/ballot.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.Ballot.LastVoteForA

theorem last_vote_for_a (m : ℤ) (hH1 : 0 < m) (n : ℤ) (hH2 : 0 < n) (hH3 : n < m) :
    {c ∈ {c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m + n) : Set ℤ) | (d.ncard : ℤ) = m} | ∀ i : ℤ, i ∈ Finset.Icc 1 (m + n) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)} | m + n ∈ c} = (fun T : Set ℤ => T ∪ ({m + n} : Set ℤ)) '' {c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m - 1 + n) : Set ℤ) | (d.ncard : ℤ) = m - 1} | ∀ i : ℤ, i ∈ Finset.Icc 1 (m - 1 + n) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)} := by
  set F : Set (Set ℤ) := {c ∈ {c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m + n) : Set ℤ) | (d.ncard : ℤ) = m} | ∀ i : ℤ, i ∈ Finset.Icc 1 (m + n) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)} | m + n ∈ c} with hD3
  have hD3_finite : F.Finite := by rw [hD3]; exact ((((Set.finite_Icc _ _).powerset).subset (fun _ h => h.1)).subset (fun _ h => h.1)).subset (fun _ h => h.1)
  -- 1. mun:nat-minus-one n := m
  have s1 : 0 ≤ m - 1 := by exact (Parley.Items.Stdlib.Numbers.mun_nat_minus_one (n := m) hH1)
  -- 2. thm:places-before-last p := (m − 1) + n, N := m + n
  have r465_1 : 1 ≤ m - 1 + n := by parley_order
  have r465_2 : m - 1 + n + 1 = m + n := by parley_ring
  have s2 : (Set.Icc (1 : ℤ) (m - 1 + n) : Set ℤ) = (Set.Icc (1 : ℤ) (m + n) : Set ℤ) \ ({m + n} : Set ℤ) := by exact (Parley.Proofs.Wiedijk.Ballot.PlacesBeforeLast.places_before_last (p := m - 1 + n) (N := m + n) r465_1 r465_2)
  -- 3. mun:difference-subset X := {1, …, m + n}, Y := {m + n}
  have s3 : (Set.Icc (1 : ℤ) (m + n) : Set ℤ) \ ({m + n} : Set ℤ) ⊆ (Set.Icc (1 : ℤ) (m + n) : Set ℤ) := by exact (Parley.Items.Stdlib.Sets.mun_difference_subset (X := (Set.Icc (1 : ℤ) (m + n) : Set ℤ)) (Y := ({m + n} : Set ℤ)))
  -- 4. substitute {1, …, (m − 1) + n} = {1, …, m + n} ∖ {m + n} (line 2) into line 3
  have s4 : (Set.Icc (1 : ℤ) (m - 1 + n) : Set ℤ) ⊆ (Set.Icc (1 : ℤ) (m + n) : Set ℤ) := by parley_subst_at s2 s3
  -- 5. algebra
  have s5 : m + n - 1 = m - 1 + n := by parley_ring
  -- 6. proof
  have s6 : ∀ c ∈ F, c ∈ (fun T : Set ℤ => T ∪ ({m + n} : Set ℤ)) '' {c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m - 1 + n) : Set ℤ) | (d.ncard : ℤ) = m - 1} | ∀ i : ℤ, i ∈ Finset.Icc 1 (m - 1 + n) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)} := by
    intro c hK1
    -- 6.1. def:set-builder u := c, from D3, K1
    have s6_1a : c ∈ {c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m + n) : Set ℤ) | (d.ncard : ℤ) = m} | ∀ i : ℤ, i ∈ Finset.Icc 1 (m + n) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)} := by
      try simp only [hD3] at ⊢
      try push_cast at ⊢
      exact (((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun c : Set ℤ => m + n ∈ c)) (X := {c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m + n) : Set ℤ) | (d.ncard : ℤ) = m} | ∀ i : ℤ, i ∈ Finset.Icc 1 (m + n) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)}) (u := c))).mp (by parley_set_side)).1
    have s6_1b : m + n ∈ c := by
      try simp only [hD3] at ⊢
      try push_cast at ⊢
      have hI : m + n ∈ c := by parley_instance ((((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun c : Set ℤ => m + n ∈ c)) (X := {c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m + n) : Set ℤ) | (d.ncard : ℤ) = m} | ∀ i : ℤ, i ∈ Finset.Icc 1 (m + n) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)}) (u := c))).mp (by parley_set_side)).2)
      exact hI
    -- 6.2. def:set-builder u := c, from D2, 6.1
    have s6_2a : c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m + n) : Set ℤ) | (d.ncard : ℤ) = m} := by exact (((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun c : Set ℤ => ∀ i : ℤ, i ∈ Finset.Icc 1 (m + n) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ))) (X := {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m + n) : Set ℤ) | (d.ncard : ℤ) = m}) (u := c))).mp (by parley_set_side)).1
    have s6_2b : ∀ i : ℤ, i ∈ Finset.Icc 1 (m + n) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ) := by
      have hI : ∀ a : ℤ, a ∈ Finset.Icc 1 (m + n) → (((Set.Icc (1 : ℤ) a : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) a : Set ℤ) ∩ c).ncard : ℤ) := by parley_instance ((((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun c : Set ℤ => ∀ i : ℤ, i ∈ Finset.Icc 1 (m + n) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ))) (X := {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m + n) : Set ℤ) | (d.ncard : ℤ) = m}) (u := c))).mp (by parley_set_side)).2)
      exact hI
    -- 6.3. D1, from 6.2
    have s6_3 : ∀ i : ℤ, i ∈ Finset.Icc 1 (m + n) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ) := by parley_set_side
    -- 6.4. def:part-builder u := c, from 6.2
    have s6_4a : c ⊆ (Set.Icc (1 : ℤ) (m + n) : Set ℤ) := by exact (((Parley.Items.Stdlib.Sets.def_part_builder (P := (fun d : Set ℤ => (d.ncard : ℤ) = m)) (X := (Set.Icc (1 : ℤ) (m + n) : Set ℤ)) (u := c))).mp (by parley_set_side)).1
    have s6_4b : (c.ncard : ℤ) = m := by
      have hI : (c.ncard : ℤ) = m := by parley_instance ((((Parley.Items.Stdlib.Sets.def_part_builder (P := (fun d : Set ℤ => (d.ncard : ℤ) = m)) (X := (Set.Icc (1 : ℤ) (m + n) : Set ℤ)) (u := c))).mp (by parley_set_side)).2)
      exact hI
    -- 6.5. mun:difference-shrinks, from 6.4
    have s6_5 : c \ ({m + n} : Set ℤ) ⊆ (Set.Icc (1 : ℤ) (m + n) : Set ℤ) \ ({m + n} : Set ℤ) := by exact (Parley.Items.Stdlib.Sets.mun_difference_shrinks (X := (Set.Icc (1 : ℤ) (m + n) : Set ℤ)) (Y := c) (Z := ({m + n} : Set ℤ)) (by parley_whole_side))
    -- 6.6. substitute {1, …, (m − 1) + n} = {1, …, m + n} ∖ {m + n} (line 2) into line 6.5
    have s6_6 : c \ ({m + n} : Set ℤ) ⊆ (Set.Icc (1 : ℤ) (m - 1 + n) : Set ℤ) := by parley_subst_at s2 s6_5
    -- 6.7. algebra, from 6.4
    have s6_7 : (c.ncard : ℤ) = m - 1 + 1 := by parley_count_int; (linear_combination (norm := parley_norm) s6_4b)
    -- 6.8. mun:card-remove X := c, a := m + n, k := m − 1, from 1, 6.1, 6.7
    have s6_8 : ((c \ ({m + n} : Set ℤ)).ncard : ℤ) = m - 1 := by exact (Parley.Items.Stdlib.Counting.mun_card_remove (X := c) (a := m + n) s6_1b (k := m - 1) s1 (by parley_set_side))
    -- 6.9. mun:remove-and-restore, from 6.1
    have s6_9 : c \ ({m + n} : Set ℤ) ∪ ({m + n} : Set ℤ) = c := by exact (Parley.Items.Stdlib.Sets.mun_remove_and_restore (Y := c) (a := m + n) s6_1b)
    -- 6.10. proof
    have s6_10 : ∀ i : ℤ, i ∈ Finset.Icc 1 (m - 1 + n) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ (c \ ({m + n} : Set ℤ))).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ (c \ ({m + n} : Set ℤ))).ncard : ℤ) := by
      intro i hK2
      try push_cast at hK2
      try have hK2_bounds := Finset.mem_Icc.mp hK2
      -- 6.10.1. mun:range-bounds a := 1, b := (m − 1) + n, k := i, from K2
      have s6_10_1 : i ≤ m - 1 + n := by exact (Parley.Items.Stdlib.Sums.mun_range_bounds_2 (a := (1 : ℤ)) (b := m - 1 + n) (k := i) hK2)
      -- 6.10.2. inequalities, from 6.10.1
      have s6_10_2 : i < m + n := by parley_order
      -- 6.10.3. mun:in-subset X := {1, …, (m − 1) + n}, Y := {1, …, m + n}, u := i, from K2, 4
      have s6_10_3 : i ∈ Finset.Icc (1 : ℤ) (m + n) := by
        have hI : i ∈ Finset.Icc (1 : ℤ) (m + n) := by parley_instance ((Parley.Items.Stdlib.Sets.mun_in_subset (X := (Set.Icc (1 : ℤ) (m - 1 + n) : Set ℤ)) (Y := (Set.Icc (1 : ℤ) (m + n) : Set ℤ)) (u := i) (by parley_whole_side) (by parley_whole_side)))
        exact hI
      -- 6.10.4. instantiate i := i in line 6.3, from 6.10.3
      have s6_10_4 : (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ) := by exact (s6_3 i s6_10_3)
      -- 6.10.5. thm:prefix-unchanged T := c ∖ {m + n}, p := m + n, from 6.10.2
      have s6_10_5a : (Set.Icc (1 : ℤ) i : Set ℤ) ∩ (c \ ({m + n} : Set ℤ) ∪ ({m + n} : Set ℤ)) = (Set.Icc (1 : ℤ) i : Set ℤ) ∩ (c \ ({m + n} : Set ℤ)) := by exact (Parley.Proofs.Wiedijk.Ballot.PrefixUnchanged.prefix_unchanged (T := c \ ({m + n} : Set ℤ)) (i := i) (p := m + n) s6_10_2).1
      have s6_10_5b : (Set.Icc (1 : ℤ) i : Set ℤ) \ (c \ ({m + n} : Set ℤ) ∪ ({m + n} : Set ℤ)) = (Set.Icc (1 : ℤ) i : Set ℤ) \ (c \ ({m + n} : Set ℤ)) := by exact (Parley.Proofs.Wiedijk.Ballot.PrefixUnchanged.prefix_unchanged (T := c \ ({m + n} : Set ℤ)) (i := i) (p := m + n) s6_10_2).2
      -- 6.10.6. substitute (c ∖ {m + n}) ∪ {m + n} = c (line 6.9) into line 6.10.5
      have s6_10_6 : (Set.Icc (1 : ℤ) i : Set ℤ) ∩ c = (Set.Icc (1 : ℤ) i : Set ℤ) ∩ (c \ ({m + n} : Set ℤ)) := by parley_subst_at s6_9 s6_10_5a
      -- 6.10.7. substitute (c ∖ {m + n}) ∪ {m + n} = c (line 6.9) into line 6.10.5
      have s6_10_7 : (Set.Icc (1 : ℤ) i : Set ℤ) \ c = (Set.Icc (1 : ℤ) i : Set ℤ) \ (c \ ({m + n} : Set ℤ)) := by parley_subst_at s6_9 s6_10_5b
      -- 6.10.8. substitute {1, …, i} ∩ c = {1, …, i} ∩ (c ∖ {m + n}) (line 6.10.6) into line 6.10.4
      have s6_10_8 : (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ (c \ ({m + n} : Set ℤ))).ncard : ℤ) := by parley_subst_at s6_10_6 s6_10_4
      -- 6.10.9. substitute {1, …, i} ∖ c = {1, …, i} ∖ (c ∖ {m + n}) (line 6.10.7) into line 6.10.8
      parley_subst_at s6_10_7 s6_10_8
    -- 6.11. D1, from 6.10
    have s6_11 : ∀ i : ℤ, i ∈ Finset.Icc 1 (m - 1 + n) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ (c \ ({m + n} : Set ℤ))).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ (c \ ({m + n} : Set ℤ))).ncard : ℤ) := by parley_set_side
    -- 6.12. def:part-builder u := c ∖ {m + n}, X := {1, …, (m − 1) + n}, from 6.6, 6.8
    have s6_12 : c \ ({m + n} : Set ℤ) ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m - 1 + n) : Set ℤ) | (d.ncard : ℤ) = m - 1} := ((Parley.Items.Stdlib.Sets.def_part_builder (P := (fun d : Set ℤ => (d.ncard : ℤ) = m - 1)) (X := (Set.Icc (1 : ℤ) (m - 1 + n) : Set ℤ)) (u := c \ ({m + n} : Set ℤ)))).mpr ⟨s6_6, by parley_set_side⟩
    -- 6.13. def:set-builder u := c ∖ {m + n}, from D2, 1, 6.11, 6.12
    have s6_13 : c \ ({m + n} : Set ℤ) ∈ {c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m - 1 + n) : Set ℤ) | (d.ncard : ℤ) = m - 1} | ∀ i : ℤ, i ∈ Finset.Icc 1 (m - 1 + n) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)} := ((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun c : Set ℤ => ∀ i : ℤ, i ∈ Finset.Icc 1 (m - 1 + n) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ))) (X := {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m - 1 + n) : Set ℤ) | (d.ncard : ℤ) = m - 1}) (u := c \ ({m + n} : Set ℤ)))).mpr ⟨by parley_set_side, by parley_set_side⟩
    -- 6.14. mun:added-element-in-image Y := G(m − 1, n), a := m + n, s := c ∖ {m + n}, from 6.13
    have s6_14 : c \ ({m + n} : Set ℤ) ∪ ({m + n} : Set ℤ) ∈ (fun T : Set ℤ => T ∪ ({m + n} : Set ℤ)) '' {c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m - 1 + n) : Set ℤ) | (d.ncard : ℤ) = m - 1} | ∀ i : ℤ, i ∈ Finset.Icc 1 (m - 1 + n) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)} := by exact (Parley.Items.Stdlib.Functions.mun_added_element_in_image (Y := {c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m - 1 + n) : Set ℤ) | (d.ncard : ℤ) = m - 1} | ∀ i : ℤ, i ∈ Finset.Icc 1 (m - 1 + n) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)}) (s := c \ ({m + n} : Set ℤ)) (a := m + n) (by parley_set_side))
    -- 6.15. substitute (c ∖ {m + n}) ∪ {m + n} = c (line 6.9) into line 6.14
    parley_subst_at s6_9 s6_14
  -- 7. def:subset, from 6
  have s7 : F ⊆ (fun T : Set ℤ => T ∪ ({m + n} : Set ℤ)) '' {c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m - 1 + n) : Set ℤ) | (d.ncard : ℤ) = m - 1} | ∀ i : ℤ, i ∈ Finset.Icc 1 (m - 1 + n) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)} := ((Parley.Items.Stdlib.Sets.def_subset (X := F) (Y := (fun T : Set ℤ => T ∪ ({m + n} : Set ℤ)) '' {c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m - 1 + n) : Set ℤ) | (d.ncard : ℤ) = m - 1} | ∀ i : ℤ, i ∈ Finset.Icc 1 (m - 1 + n) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)}))).mpr (by parley_set_side)
  -- 8. proof
  have s8 : ∀ T ∈ {c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m - 1 + n) : Set ℤ) | (d.ncard : ℤ) = m - 1} | ∀ i : ℤ, i ∈ Finset.Icc 1 (m - 1 + n) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)}, T ∪ ({m + n} : Set ℤ) ∈ F := by
    intro T hK3
    -- 8.1. def:set-builder u := T, from D2, K3, 1
    have s8_1a : T ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m - 1 + n) : Set ℤ) | (d.ncard : ℤ) = m - 1} := by exact (((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun c : Set ℤ => ∀ i : ℤ, i ∈ Finset.Icc 1 (m - 1 + n) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ))) (X := {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m - 1 + n) : Set ℤ) | (d.ncard : ℤ) = m - 1}) (u := T))).mp (by parley_set_side)).1
    have s8_1b : ∀ i : ℤ, i ∈ Finset.Icc 1 (m - 1 + n) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ T).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ T).ncard : ℤ) := by
      have hI : ∀ a : ℤ, a ∈ Finset.Icc 1 (m - 1 + n) → (((Set.Icc (1 : ℤ) a : Set ℤ) \ T).ncard : ℤ) < (((Set.Icc (1 : ℤ) a : Set ℤ) ∩ T).ncard : ℤ) := by parley_instance ((((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun c : Set ℤ => ∀ i : ℤ, i ∈ Finset.Icc 1 (m - 1 + n) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ))) (X := {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m - 1 + n) : Set ℤ) | (d.ncard : ℤ) = m - 1}) (u := T))).mp (by parley_set_side)).2)
      exact hI
    -- 8.2. def:part-builder u := T, from 8.1
    have s8_2a : T ⊆ (Set.Icc (1 : ℤ) (m - 1 + n) : Set ℤ) := by exact (((Parley.Items.Stdlib.Sets.def_part_builder (P := (fun d : Set ℤ => (d.ncard : ℤ) = m - 1)) (X := (Set.Icc (1 : ℤ) (m - 1 + n) : Set ℤ)) (u := T))).mp (by parley_set_side)).1
    have s8_2b : (T.ncard : ℤ) = m - 1 := by
      have hI : (T.ncard : ℤ) = m - 1 := by parley_instance ((((Parley.Items.Stdlib.Sets.def_part_builder (P := (fun d : Set ℤ => (d.ncard : ℤ) = m - 1)) (X := (Set.Icc (1 : ℤ) (m - 1 + n) : Set ℤ)) (u := T))).mp (by parley_set_side)).2)
      exact hI
    -- 8.3. substitute {1, …, (m − 1) + n} = {1, …, m + n} ∖ {m + n} (line 2) into line 8.2
    have s8_3 : T ⊆ (Set.Icc (1 : ℤ) (m + n) : Set ℤ) \ ({m + n} : Set ℤ) := by parley_subst_at s2 s8_2a
    -- 8.4. mun:subset-of-difference, from 8.3
    have s8_4 : ¬ m + n ∈ T := by exact (Parley.Items.Stdlib.Sets.mun_subset_of_difference (X := (Set.Icc (1 : ℤ) (m + n) : Set ℤ)) (Y := T) (a := m + n) (by parley_whole_side))
    -- 8.5. mun:subset-transitive, from 4, 8.2
    have s8_5 : T ⊆ (Set.Icc (1 : ℤ) (m + n) : Set ℤ) := by exact (Parley.Items.Stdlib.Sets.mun_subset_transitive (X := T) (Y := (Set.Icc (1 : ℤ) (m - 1 + n) : Set ℤ)) (Z := (Set.Icc (1 : ℤ) (m + n) : Set ℤ)) (by parley_whole_side) (by parley_whole_side))
    -- 8.6. mun:range-end n := m + n
    have s8_6 : m + n ∈ Finset.Icc (1 : ℤ) (m + n) := by exact (Parley.Items.Stdlib.Sums.mun_range_end (n := m + n) (by parley_set_side))
    -- 8.7. mun:singleton-subset, from 8.6
    have s8_7 : ({m + n} : Set ℤ) ⊆ (Set.Icc (1 : ℤ) (m + n) : Set ℤ) := by exact (Parley.Items.Stdlib.Sets.mun_singleton_subset (X := (Set.Icc (1 : ℤ) (m + n) : Set ℤ)) (a := m + n) (by parley_whole_side))
    -- 8.8. mun:union-subset, from 8.5, 8.7
    have s8_8 : T ∪ ({m + n} : Set ℤ) ⊆ (Set.Icc (1 : ℤ) (m + n) : Set ℤ) := by exact (Parley.Items.Stdlib.Sets.mun_union_subset (X := T) (Y := ({m + n} : Set ℤ)) (Z := (Set.Icc (1 : ℤ) (m + n) : Set ℤ)) (by parley_whole_side) (by parley_whole_side))
    -- 8.9. mun:range-finite a := 1, b := (m − 1) + n
    have s8_9 : (Set.Icc (1 : ℤ) (m - 1 + n) : Set ℤ).Finite := by exact (Parley.Items.Stdlib.Sums.mun_range_finite (a := (1 : ℤ)) (b := m - 1 + n))
    -- 8.10. mun:finite-part X := {1, …, (m − 1) + n}, Y := T, from 8.2, 8.9
    have s8_10 : T.Finite := by exact (Parley.Items.Stdlib.Counting.mun_finite_part (X := (Set.Icc (1 : ℤ) (m - 1 + n) : Set ℤ)) (Y := T) (by parley_whole_side) (by parley_whole_side))
    -- 8.11. mun:card-add-one, from 8.4, 8.10
    have s8_11 : ((T ∪ ({m + n} : Set ℤ)).ncard : ℤ) = (T.ncard : ℤ) + 1 := by exact (Parley.Items.Stdlib.Counting.mun_card_add_one (X := T) (a := m + n) s8_10 s8_4)
    -- 8.12. algebra, from 8.2, 8.11
    have s8_12 : ((T ∪ ({m + n} : Set ℤ)).ncard : ℤ) = m := by parley_count_int; (linear_combination (norm := parley_norm) s8_2b + s8_11)
    -- 8.13. proof
    have s8_13 : ∀ i : ℤ, i ∈ Finset.Icc 1 (m + n - 1) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ (T ∪ ({m + n} : Set ℤ))).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ (T ∪ ({m + n} : Set ℤ))).ncard : ℤ) := by
      intro i hK4
      try push_cast at hK4
      try have hK4_bounds := Finset.mem_Icc.mp hK4
      -- 8.13.1. D1, from 8.1
      have s8_13_1 : ∀ j : ℤ, j ∈ Finset.Icc 1 (m - 1 + n) → (((Set.Icc (1 : ℤ) j : Set ℤ) \ T).ncard : ℤ) < (((Set.Icc (1 : ℤ) j : Set ℤ) ∩ T).ncard : ℤ) := by parley_set_side
      -- 8.13.2. mun:range-bounds a := 1, b := (m + n) − 1, k := i, from K4
      have s8_13_2 : i ≤ m + n - 1 := by exact (Parley.Items.Stdlib.Sums.mun_range_bounds_2 (a := (1 : ℤ)) (b := m + n - 1) (k := i) hK4)
      -- 8.13.3. inequalities, from 8.13.2
      have s8_13_3 : i < m + n := by parley_order
      -- 8.13.4. substitute (m + n) − 1 = (m − 1) + n (line 5) into K4
      have s8_13_4 : i ∈ Finset.Icc (1 : ℤ) (m - 1 + n) := by (have h := Eq.subst (motive := (fun t : ℤ => i ∈ Finset.Icc (1 : ℤ) t)) s5 hK4; push_cast at h ⊢; all_goals exact_mod_cast h)
      -- 8.13.5. instantiate j := i in line 8.13.1, from 8.13.4
      have s8_13_5 : (((Set.Icc (1 : ℤ) i : Set ℤ) \ T).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ T).ncard : ℤ) := by exact (s8_13_1 i s8_13_4)
      -- 8.13.6. thm:prefix-unchanged p := m + n, from 8.13.3
      have s8_13_6a : (Set.Icc (1 : ℤ) i : Set ℤ) ∩ (T ∪ ({m + n} : Set ℤ)) = (Set.Icc (1 : ℤ) i : Set ℤ) ∩ T := by exact (Parley.Proofs.Wiedijk.Ballot.PrefixUnchanged.prefix_unchanged (T := T) (i := i) (p := m + n) s8_13_3).1
      have s8_13_6b : (Set.Icc (1 : ℤ) i : Set ℤ) \ (T ∪ ({m + n} : Set ℤ)) = (Set.Icc (1 : ℤ) i : Set ℤ) \ T := by exact (Parley.Proofs.Wiedijk.Ballot.PrefixUnchanged.prefix_unchanged (T := T) (i := i) (p := m + n) s8_13_3).2
      -- 8.13.7. substitute {1, …, i} ∩ (T ∪ {m + n}) = {1, …, i} ∩ T (line 8.13.6) into line 8.13.5
      have s8_13_7 : (((Set.Icc (1 : ℤ) i : Set ℤ) \ T).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ (T ∪ ({m + n} : Set ℤ))).ncard : ℤ) := by parley_subst_at s8_13_6a s8_13_5
      -- 8.13.8. substitute {1, …, i} ∖ (T ∪ {m + n}) = {1, …, i} ∖ T (line 8.13.6) into line 8.13.7
      parley_subst_at s8_13_6b s8_13_7
    -- 8.14. D1, from 8.13
    have s8_14 : ∀ i : ℤ, i ∈ Finset.Icc 1 (m + n - 1) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ (T ∪ ({m + n} : Set ℤ))).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ (T ∪ ({m + n} : Set ℤ))).ncard : ℤ) := by parley_set_side
    -- 8.15. thm:lead-to-the-end c := T ∪ {m + n}, from H3, 8.8, 8.12, 8.14
    have s8_15 : ∀ i : ℤ, i ∈ Finset.Icc 1 (m + n) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ (T ∪ ({m + n} : Set ℤ))).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ (T ∪ ({m + n} : Set ℤ))).ncard : ℤ) := by exact (Parley.Proofs.Wiedijk.Ballot.LeadToTheEnd.lead_to_the_end (m := m) (le_of_lt hH1) (n := n) (le_of_lt hH2) (c := T ∪ ({m + n} : Set ℤ)) (by parley_set_side) hH3 (by parley_set_side) (by parley_set_side))
    -- 8.16. def:part-builder u := T ∪ {m + n}, X := {1, …, m + n}, from 8.8, 8.12
    have s8_16 : T ∪ ({m + n} : Set ℤ) ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m + n) : Set ℤ) | (d.ncard : ℤ) = m} := ((Parley.Items.Stdlib.Sets.def_part_builder (P := (fun d : Set ℤ => (d.ncard : ℤ) = m)) (X := (Set.Icc (1 : ℤ) (m + n) : Set ℤ)) (u := T ∪ ({m + n} : Set ℤ)))).mpr ⟨s8_8, by parley_set_side⟩
    -- 8.17. def:set-builder u := T ∪ {m + n}, from D2, 8.15, 8.16
    have s8_17 : T ∪ ({m + n} : Set ℤ) ∈ {c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m + n) : Set ℤ) | (d.ncard : ℤ) = m} | ∀ i : ℤ, i ∈ Finset.Icc 1 (m + n) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)} := ((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun c : Set ℤ => ∀ i : ℤ, i ∈ Finset.Icc 1 (m + n) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ))) (X := {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m + n) : Set ℤ) | (d.ncard : ℤ) = m}) (u := T ∪ ({m + n} : Set ℤ)))).mpr ⟨by parley_set_side, by parley_set_side⟩
    -- 8.18. mun:in-union-singleton
    have s8_18 : m + n ∈ T ∪ ({m + n} : Set ℤ) := by exact (Parley.Items.Stdlib.Sets.mun_in_union_singleton (Y := T) (a := m + n))
    -- 8.19. def:set-builder u := T ∪ {m + n}, from D3, 8.17, 8.18
    exact ((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun c : Set ℤ => m + n ∈ c)) (X := {c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m + n) : Set ℤ) | (d.ncard : ℤ) = m} | ∀ i : ℤ, i ∈ Finset.Icc 1 (m + n) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)}) (u := T ∪ ({m + n} : Set ℤ)))).mpr ⟨by parley_set_side, s8_18⟩
  -- 9. mun:added-elements-stay-inside Y := G(m − 1, n), a := m + n, Z := F, from 8
  have s9 : (fun T : Set ℤ => T ∪ ({m + n} : Set ℤ)) '' {c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m - 1 + n) : Set ℤ) | (d.ncard : ℤ) = m - 1} | ∀ i : ℤ, i ∈ Finset.Icc 1 (m - 1 + n) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)} ⊆ F := by exact (Parley.Items.Stdlib.Functions.mun_added_elements_stay_inside (Y := {c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m - 1 + n) : Set ℤ) | (d.ncard : ℤ) = m - 1} | ∀ i : ℤ, i ∈ Finset.Icc 1 (m - 1 + n) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)}) (Z := F) (a := m + n) (by parley_set_side))
  -- 10. mun:subset-antisymmetric, from D3, 7, 9
  try simp only [hD3] at ⊢
  try push_cast at ⊢
  exact (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := {c ∈ {c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m + n) : Set ℤ) | (d.ncard : ℤ) = m} | ∀ i : ℤ, i ∈ Finset.Icc 1 (m + n) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)} | m + n ∈ c}) (Y := (fun T : Set ℤ => T ∪ ({m + n} : Set ℤ)) '' {c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m - 1 + n) : Set ℤ) | (d.ncard : ℤ) = m - 1} | ∀ i : ℤ, i ∈ Finset.Icc 1 (m - 1 + n) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)}) (by parley_set_side) (by parley_set_side))

end Parley.Proofs.Wiedijk.Ballot.LastVoteForA
