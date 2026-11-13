module

public import AlgebraTactics
public import InstanceTactics
public import SetTactics
public import SubstTactics
public import Tactics
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
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Set
public import Mathlib.Tactic.SetNotationForOrder
public import Parley.Items.Proofs.Wiedijk.Ballot
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Sets
public import Parley.Proofs.Wiedijk.Ballot.LeadToTheEnd
public import Parley.Proofs.Wiedijk.Ballot.PlacesBeforeLast

/-! Written from proofs/wiedijk/ballot.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.Ballot.LastVoteForB

theorem last_vote_for_b (m : ℤ) (hH1 : 0 < m) (n : ℤ) (hH2 : 0 < n) (hH3 : n < m) :
    {c ∈ {c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m + n) : Set ℤ) | (d.ncard : ℤ) = m} | ∀ i : ℤ, i ∈ Finset.Icc 1 (m + n) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)} | ¬ m + n ∈ c} = {c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m + (n - 1)) : Set ℤ) | (d.ncard : ℤ) = m} | ∀ i : ℤ, i ∈ Finset.Icc 1 (m + (n - 1)) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)} := by
  set F : Set (Set ℤ) := {c ∈ {c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m + n) : Set ℤ) | (d.ncard : ℤ) = m} | ∀ i : ℤ, i ∈ Finset.Icc 1 (m + n) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)} | ¬ m + n ∈ c} with hD3
  have hD3_finite : F.Finite := by rw [hD3]; exact ((((Set.finite_Icc _ _).powerset).subset (fun _ h => h.1)).subset (fun _ h => h.1)).subset (fun _ h => h.1)
  -- 1. mun:nat-minus-one
  have s1 : 0 ≤ n - 1 := by exact (Parley.Items.Stdlib.Numbers.mun_nat_minus_one (n := n) hH2)
  -- 2. thm:places-before-last p := m + (n − 1), N := m + n
  have r669_1 : 1 ≤ m + (n - 1) := by linarith only [hH1, hH2]
  have r669_2 : m + (n - 1) + 1 = m + n := by parley_ring
  have s2 : (Set.Icc (1 : ℤ) (m + (n - 1)) : Set ℤ) = (Set.Icc (1 : ℤ) (m + n) : Set ℤ) \ ({m + n} : Set ℤ) := by exact (Parley.Proofs.Wiedijk.Ballot.PlacesBeforeLast.places_before_last (p := m + (n - 1)) (N := m + n) r669_1 r669_2)
  -- 3. mun:difference-subset X := {1, …, m + n}, Y := {m + n}
  have s3 : (Set.Icc (1 : ℤ) (m + n) : Set ℤ) \ ({m + n} : Set ℤ) ⊆ (Set.Icc (1 : ℤ) (m + n) : Set ℤ) := by exact (Parley.Items.Stdlib.Sets.mun_difference_subset (X := (Set.Icc (1 : ℤ) (m + n) : Set ℤ)) (Y := ({m + n} : Set ℤ)))
  -- 4. substitute {1, …, m + (n − 1)} = {1, …, m + n} ∖ {m + n} (line 2) into line 3
  have s4 : (Set.Icc (1 : ℤ) (m + (n - 1)) : Set ℤ) ⊆ (Set.Icc (1 : ℤ) (m + n) : Set ℤ) := by parley_subst_at s2 s3
  -- 5. algebra
  have s5 : m + n - 1 = m + (n - 1) := by parley_ring
  -- 6. proof
  have s6 : ∀ c ∈ F, c ∈ {c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m + (n - 1)) : Set ℤ) | (d.ncard : ℤ) = m} | ∀ i : ℤ, i ∈ Finset.Icc 1 (m + (n - 1)) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)} := by
    intro c hK1
    -- 6.1. def:set-builder u := c, from D3, K1
    have s6_1a : c ∈ {c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m + n) : Set ℤ) | (d.ncard : ℤ) = m} | ∀ i : ℤ, i ∈ Finset.Icc 1 (m + n) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)} := by
      try simp only [hD3] at ⊢
      try push_cast at ⊢
      exact (((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun c : Set ℤ => ¬ m + n ∈ c)) (X := {c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m + n) : Set ℤ) | (d.ncard : ℤ) = m} | ∀ i : ℤ, i ∈ Finset.Icc 1 (m + n) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)}) (u := c))).mp hK1).1
    have s6_1b : ¬ m + n ∈ c := by
      try simp only [hD3] at ⊢
      try push_cast at ⊢
      have hI : ¬ m + n ∈ c := by parley_instance ((((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun c : Set ℤ => ¬ m + n ∈ c)) (X := {c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m + n) : Set ℤ) | (d.ncard : ℤ) = m} | ∀ i : ℤ, i ∈ Finset.Icc 1 (m + n) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)}) (u := c))).mp hK1).2)
      exact hI
    -- 6.2. def:set-builder u := c, from D2, 6.1
    have s6_2a : c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m + n) : Set ℤ) | (d.ncard : ℤ) = m} := by exact (((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun c : Set ℤ => ∀ i : ℤ, i ∈ Finset.Icc 1 (m + n) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ))) (X := {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m + n) : Set ℤ) | (d.ncard : ℤ) = m}) (u := c))).mp s6_1a).1
    have s6_2b : ∀ i : ℤ, i ∈ Finset.Icc 1 (m + n) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ) := by
      have hI : ∀ a : ℤ, a ∈ Finset.Icc 1 (m + n) → (((Set.Icc (1 : ℤ) a : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) a : Set ℤ) ∩ c).ncard : ℤ) := by parley_instance ((((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun c : Set ℤ => ∀ i : ℤ, i ∈ Finset.Icc 1 (m + n) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ))) (X := {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m + n) : Set ℤ) | (d.ncard : ℤ) = m}) (u := c))).mp s6_1a).2)
      exact hI
    -- 6.3. D1, from 6.2
    have s6_3 : ∀ i : ℤ, i ∈ Finset.Icc 1 (m + n) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ) := by parley_set_side
    -- 6.4. def:part-builder u := c, from 6.2
    have s6_4a : c ⊆ (Set.Icc (1 : ℤ) (m + n) : Set ℤ) := by exact (((Parley.Items.Stdlib.Sets.def_part_builder (P := (fun d : Set ℤ => (d.ncard : ℤ) = m)) (X := (Set.Icc (1 : ℤ) (m + n) : Set ℤ)) (u := c))).mp s6_2a).1
    have s6_4b : (c.ncard : ℤ) = m := by
      have hI : (c.ncard : ℤ) = m := by parley_instance ((((Parley.Items.Stdlib.Sets.def_part_builder (P := (fun d : Set ℤ => (d.ncard : ℤ) = m)) (X := (Set.Icc (1 : ℤ) (m + n) : Set ℤ)) (u := c))).mp s6_2a).2)
      exact hI
    -- 6.5. mun:subset-into-difference, from 6.1, 6.4
    have s6_5 : c ⊆ (Set.Icc (1 : ℤ) (m + n) : Set ℤ) \ ({m + n} : Set ℤ) := by exact (Parley.Items.Stdlib.Sets.mun_subset_into_difference (X := (Set.Icc (1 : ℤ) (m + n) : Set ℤ)) (Y := c) (a := m + n) s6_4a s6_1b)
    -- 6.6. substitute {1, …, m + (n − 1)} = {1, …, m + n} ∖ {m + n} (line 2) into line 6.5
    have s6_6 : c ⊆ (Set.Icc (1 : ℤ) (m + (n - 1)) : Set ℤ) := by parley_subst_at s2 s6_5
    -- 6.7. proof
    have s6_7 : ∀ i : ℤ, i ∈ Finset.Icc 1 (m + (n - 1)) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ) := by
      intro i hK2
      try push_cast at hK2
      try have hK2_bounds := Finset.mem_Icc.mp hK2
      -- 6.7.1. mun:in-subset X := {1, …, m + (n − 1)}, Y := {1, …, m + n}, u := i, from K2, 4
      have s6_7_1 : i ∈ Finset.Icc (1 : ℤ) (m + n) := by
        have hI : i ∈ Finset.Icc (1 : ℤ) (m + n) := by parley_instance ((Parley.Items.Stdlib.Sets.mun_in_subset (X := (Set.Icc (1 : ℤ) (m + (n - 1)) : Set ℤ)) (Y := (Set.Icc (1 : ℤ) (m + n) : Set ℤ)) (u := i) s4 (by simpa only [Finset.mem_Icc, Set.mem_Icc] using hK2)))
        exact hI
      -- 6.7.2. instantiate i := i in line 6.3, from 6.7.1
      exact (s6_3 i s6_7_1)
    -- 6.8. D1, from 6.7
    have s6_8 : ∀ i : ℤ, i ∈ Finset.Icc 1 (m + (n - 1)) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ) := by parley_set_side
    -- 6.9. def:part-builder u := c, X := {1, …, m + (n − 1)}, from 6.4, 6.6
    have s6_9 : c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m + (n - 1)) : Set ℤ) | (d.ncard : ℤ) = m} := ((Parley.Items.Stdlib.Sets.def_part_builder (P := (fun d : Set ℤ => (d.ncard : ℤ) = m)) (X := (Set.Icc (1 : ℤ) (m + (n - 1)) : Set ℤ)) (u := c))).mpr ⟨s6_6, s6_4b⟩
    -- 6.10. def:set-builder u := c, from D2, 1, 6.8, 6.9
    exact ((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun c : Set ℤ => ∀ i : ℤ, i ∈ Finset.Icc 1 (m + (n - 1)) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ))) (X := {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m + (n - 1)) : Set ℤ) | (d.ncard : ℤ) = m}) (u := c))).mpr ⟨s6_9, s6_8⟩
  -- 7. def:subset, from 6
  have s7 : F ⊆ {c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m + (n - 1)) : Set ℤ) | (d.ncard : ℤ) = m} | ∀ i : ℤ, i ∈ Finset.Icc 1 (m + (n - 1)) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)} := ((Parley.Items.Stdlib.Sets.def_subset (X := F) (Y := {c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m + (n - 1)) : Set ℤ) | (d.ncard : ℤ) = m} | ∀ i : ℤ, i ∈ Finset.Icc 1 (m + (n - 1)) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)}))).mpr s6
  -- 8. proof
  have s8 : ∀ c ∈ {c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m + (n - 1)) : Set ℤ) | (d.ncard : ℤ) = m} | ∀ i : ℤ, i ∈ Finset.Icc 1 (m + (n - 1)) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)}, c ∈ F := by
    intro c hK3
    -- 8.1. def:set-builder u := c, from D2, K3, 1
    have s8_1a : c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m + (n - 1)) : Set ℤ) | (d.ncard : ℤ) = m} := by exact (((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun c : Set ℤ => ∀ i : ℤ, i ∈ Finset.Icc 1 (m + (n - 1)) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ))) (X := {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m + (n - 1)) : Set ℤ) | (d.ncard : ℤ) = m}) (u := c))).mp hK3).1
    have s8_1b : ∀ i : ℤ, i ∈ Finset.Icc 1 (m + (n - 1)) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ) := by
      have hI : ∀ a : ℤ, a ∈ Finset.Icc 1 (m + (n - 1)) → (((Set.Icc (1 : ℤ) a : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) a : Set ℤ) ∩ c).ncard : ℤ) := by parley_instance ((((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun c : Set ℤ => ∀ i : ℤ, i ∈ Finset.Icc 1 (m + (n - 1)) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ))) (X := {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m + (n - 1)) : Set ℤ) | (d.ncard : ℤ) = m}) (u := c))).mp hK3).2)
      exact hI
    -- 8.2. def:part-builder u := c, from 8.1
    have s8_2a : c ⊆ (Set.Icc (1 : ℤ) (m + (n - 1)) : Set ℤ) := by exact (((Parley.Items.Stdlib.Sets.def_part_builder (P := (fun d : Set ℤ => (d.ncard : ℤ) = m)) (X := (Set.Icc (1 : ℤ) (m + (n - 1)) : Set ℤ)) (u := c))).mp s8_1a).1
    have s8_2b : (c.ncard : ℤ) = m := by
      have hI : (c.ncard : ℤ) = m := by parley_instance ((((Parley.Items.Stdlib.Sets.def_part_builder (P := (fun d : Set ℤ => (d.ncard : ℤ) = m)) (X := (Set.Icc (1 : ℤ) (m + (n - 1)) : Set ℤ)) (u := c))).mp s8_1a).2)
      exact hI
    -- 8.3. mun:subset-transitive, from 4, 8.2
    have s8_3 : c ⊆ (Set.Icc (1 : ℤ) (m + n) : Set ℤ) := by exact (Parley.Items.Stdlib.Sets.mun_subset_transitive (X := c) (Y := (Set.Icc (1 : ℤ) (m + (n - 1)) : Set ℤ)) (Z := (Set.Icc (1 : ℤ) (m + n) : Set ℤ)) s8_2a s4)
    -- 8.4. substitute {1, …, m + (n − 1)} = {1, …, m + n} ∖ {m + n} (line 2) into line 8.2
    have s8_4 : c ⊆ (Set.Icc (1 : ℤ) (m + n) : Set ℤ) \ ({m + n} : Set ℤ) := by parley_subst_at s2 s8_2a
    -- 8.5. mun:subset-of-difference, from 8.4
    have s8_5 : ¬ m + n ∈ c := by exact (Parley.Items.Stdlib.Sets.mun_subset_of_difference (X := (Set.Icc (1 : ℤ) (m + n) : Set ℤ)) (Y := c) (a := m + n) s8_4)
    -- 8.6. substitute (m + n) − 1 = m + (n − 1) (line 5) into line 8.1
    have s8_6 : ∀ i : ℤ, i ∈ Finset.Icc 1 (m + n - 1) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ) := by (have h := Eq.subst (motive := (fun t : ℤ => ∀ i : ℤ, i ∈ Finset.Icc 1 t → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ))) s5.symm s8_1b; push_cast at h ⊢; all_goals exact_mod_cast h)
    -- 8.7. thm:lead-to-the-end, from H3, 8.2, 8.3, 8.6
    have s8_7 : ∀ i : ℤ, i ∈ Finset.Icc 1 (m + n) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ) := by exact (Parley.Proofs.Wiedijk.Ballot.LeadToTheEnd.lead_to_the_end (m := m) (le_of_lt hH1) (n := n) (le_of_lt hH2) (c := c) s8_3 hH3 s8_2b s8_6)
    -- 8.8. def:part-builder u := c, X := {1, …, m + n}, from 8.2, 8.3
    have s8_8 : c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m + n) : Set ℤ) | (d.ncard : ℤ) = m} := ((Parley.Items.Stdlib.Sets.def_part_builder (P := (fun d : Set ℤ => (d.ncard : ℤ) = m)) (X := (Set.Icc (1 : ℤ) (m + n) : Set ℤ)) (u := c))).mpr ⟨s8_3, s8_2b⟩
    -- 8.9. def:set-builder u := c, from D2, 8.7, 8.8
    have s8_9 : c ∈ {c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m + n) : Set ℤ) | (d.ncard : ℤ) = m} | ∀ i : ℤ, i ∈ Finset.Icc 1 (m + n) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)} := ((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun c : Set ℤ => ∀ i : ℤ, i ∈ Finset.Icc 1 (m + n) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ))) (X := {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m + n) : Set ℤ) | (d.ncard : ℤ) = m}) (u := c))).mpr ⟨s8_8, s8_7⟩
    -- 8.10. def:set-builder u := c, from D3, 8.5, 8.9
    exact ((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun c : Set ℤ => ¬ m + n ∈ c)) (X := {c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m + n) : Set ℤ) | (d.ncard : ℤ) = m} | ∀ i : ℤ, i ∈ Finset.Icc 1 (m + n) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)}) (u := c))).mpr ⟨s8_9, s8_5⟩
  -- 9. def:subset, from 8
  have s9 : {c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m + (n - 1)) : Set ℤ) | (d.ncard : ℤ) = m} | ∀ i : ℤ, i ∈ Finset.Icc 1 (m + (n - 1)) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)} ⊆ F := ((Parley.Items.Stdlib.Sets.def_subset (X := {c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m + (n - 1)) : Set ℤ) | (d.ncard : ℤ) = m} | ∀ i : ℤ, i ∈ Finset.Icc 1 (m + (n - 1)) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)}) (Y := F))).mpr s8
  -- 10. mun:subset-antisymmetric, from D3, 7, 9
  try simp only [hD3] at ⊢
  try push_cast at ⊢
  exact (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := {c ∈ {c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m + n) : Set ℤ) | (d.ncard : ℤ) = m} | ∀ i : ℤ, i ∈ Finset.Icc 1 (m + n) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)} | ¬ m + n ∈ c}) (Y := {c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m + (n - 1)) : Set ℤ) | (d.ncard : ℤ) = m} | ∀ i : ℤ, i ∈ Finset.Icc 1 (m + (n - 1)) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)}) s7 s9)

end Parley.Proofs.Wiedijk.Ballot.LastVoteForB
