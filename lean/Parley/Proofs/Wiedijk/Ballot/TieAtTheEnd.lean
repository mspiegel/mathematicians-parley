module

public import ArithTactics
public import NormTactics
public import PowerTactics
public import SetTactics
public import Tactics
public import Batteries.Tactic.Init
public import Batteries.Util.ExtendedBinder
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Set
public import Mathlib.Tactic.SetNotationForOrder
public import Parley.Items.Proofs.Wiedijk.Ballot
public import Parley.Items.Stdlib.Sets
public import Parley.Items.Stdlib.Sums
public import Parley.Proofs.Wiedijk.Ballot.LastPlace

/-! Written from proofs/wiedijk/ballot.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.Ballot.TieAtTheEnd

theorem tie_at_the_end (m : ℤ) (hH1 : 0 < m) :
    {c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m + m) : Set ℤ) | (d.ncard : ℤ) = m} | ∀ i : ℤ, i ∈ Finset.Icc 1 (m + m) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)} = ∅ := by
  set O : Set (Set ℤ) := {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m + m) : Set ℤ) | (d.ncard : ℤ) = m} with hD3
  have hD3_finite : O.Finite := by rw [hD3]; exact ((Set.finite_Icc _ _).powerset).subset (fun _ h => h.1)
  -- 1. mun:range-end n := m + m
  have s1 : m + m ∈ Finset.Icc (1 : ℤ) (m + m) := by exact (Parley.Items.Stdlib.Sums.mun_range_end (n := m + m) (by parley_set_side))
  -- 2. proof
  have s2 : ∀ c ∈ O, ¬ (∀ i : ℤ, i ∈ Finset.Icc 1 (m + m) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)) := by
    intro c hK1
    by_contra hc_hS1
    have hS1 : ∀ i : ℤ, i ∈ Finset.Icc 1 (m + m) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ) := by parley_suppose hc_hS1
    -- 2.1. def:part-builder u := c, from D3, K1
    have s2_1a : c ⊆ (Set.Icc (1 : ℤ) (m + m) : Set ℤ) := by
      try simp only [hD3] at *
      try push_cast at *
      first | exact (((Parley.Items.Stdlib.Sets.def_part_builder (P := (fun d : Set ℤ => (d.ncard : ℤ) = m)) (X := (Set.Icc (1 : ℤ) (m + m) : Set ℤ)) (u := c))).mp (by parley_set_side)).1 | exact ((((Parley.Items.Stdlib.Sets.def_part_builder (P := (fun d : Set ℤ => (d.ncard : ℤ) = m)) (X := (Set.Icc (1 : ℤ) (m + m) : Set ℤ)) (u := c))).mp (by parley_set_side)).1).symm | simpa using (((Parley.Items.Stdlib.Sets.def_part_builder (P := (fun d : Set ℤ => (d.ncard : ℤ) = m)) (X := (Set.Icc (1 : ℤ) (m + m) : Set ℤ)) (u := c))).mp (by parley_set_side)).1 | exact_mod_cast (((Parley.Items.Stdlib.Sets.def_part_builder (P := (fun d : Set ℤ => (d.ncard : ℤ) = m)) (X := (Set.Icc (1 : ℤ) (m + m) : Set ℤ)) (u := c))).mp (by parley_set_side)).1 | (have h := (((Parley.Items.Stdlib.Sets.def_part_builder (P := (fun d : Set ℤ => (d.ncard : ℤ) = m)) (X := (Set.Icc (1 : ℤ) (m + m) : Set ℤ)) (u := c))).mp (by parley_set_side)).1; parley_set_side)
    have s2_1b : (c.ncard : ℤ) = m := by
      try simp only [hD3] at *
      try push_cast at *
      first | linear_combination (norm := parley_norm) (((Parley.Items.Stdlib.Sets.def_part_builder (P := (fun d : Set ℤ => (d.ncard : ℤ) = m)) (X := (Set.Icc (1 : ℤ) (m + m) : Set ℤ)) (u := c))).mp (by parley_set_side)).2 | (have h := (((Parley.Items.Stdlib.Sets.def_part_builder (P := (fun d : Set ℤ => (d.ncard : ℤ) = m)) (X := (Set.Icc (1 : ℤ) (m + m) : Set ℤ)) (u := c))).mp (by parley_set_side)).2; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (((Parley.Items.Stdlib.Sets.def_part_builder (P := (fun d : Set ℤ => (d.ncard : ℤ) = m)) (X := (Set.Icc (1 : ℤ) (m + m) : Set ℤ)) (u := c))).mp (by parley_set_side)).2; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | (parley_count_ext; exact_mod_cast (((Parley.Items.Stdlib.Sets.def_part_builder (P := (fun d : Set ℤ => (d.ncard : ℤ) = m)) (X := (Set.Icc (1 : ℤ) (m + m) : Set ℤ)) (u := c))).mp (by parley_set_side)).2) | exact_mod_cast (((Parley.Items.Stdlib.Sets.def_part_builder (P := (fun d : Set ℤ => (d.ncard : ℤ) = m)) (X := (Set.Icc (1 : ℤ) (m + m) : Set ℤ)) (u := c))).mp (by parley_set_side)).2 | exact_mod_cast ((((Parley.Items.Stdlib.Sets.def_part_builder (P := (fun d : Set ℤ => (d.ncard : ℤ) = m)) (X := (Set.Icc (1 : ℤ) (m + m) : Set ℤ)) (u := c))).mp (by parley_set_side)).2).symm | (have h := (((Parley.Items.Stdlib.Sets.def_part_builder (P := (fun d : Set ℤ => (d.ncard : ℤ) = m)) (X := (Set.Icc (1 : ℤ) (m + m) : Set ℤ)) (u := c))).mp (by parley_set_side)).2; rify; linear_combination (norm := parley_norm) h) | (have h := (((Parley.Items.Stdlib.Sets.def_part_builder (P := (fun d : Set ℤ => (d.ncard : ℤ) = m)) (X := (Set.Icc (1 : ℤ) (m + m) : Set ℤ)) (u := c))).mp (by parley_set_side)).2; qify; linear_combination (norm := parley_norm) h) | (have h := (((Parley.Items.Stdlib.Sets.def_part_builder (P := (fun d : Set ℤ => (d.ncard : ℤ) = m)) (X := (Set.Icc (1 : ℤ) (m + m) : Set ℤ)) (u := c))).mp (by parley_set_side)).2; parley_int_power h) | (have h := (((Parley.Items.Stdlib.Sets.def_part_builder (P := (fun d : Set ℤ => (d.ncard : ℤ) = m)) (X := (Set.Icc (1 : ℤ) (m + m) : Set ℤ)) (u := c))).mp (by parley_set_side)).2; parley_set_side)
    -- 2.2. thm:last-place n := m, from 2.1
    have s2_2a : (((Set.Icc (1 : ℤ) (m + m) : Set ℤ) \ c).ncard : ℤ) = m := by exact (Parley.Proofs.Wiedijk.Ballot.LastPlace.last_place (m := m) (by parley_set_side) (n := m) (by parley_set_side) (c := c) s2_1a s2_1b).1
    have s2_2b : (((Set.Icc (1 : ℤ) (m + m) : Set ℤ) ∩ c).ncard : ℤ) = m := by exact (Parley.Proofs.Wiedijk.Ballot.LastPlace.last_place (m := m) (by parley_set_side) (n := m) (by parley_set_side) (c := c) s2_1a s2_1b).2
    -- 2.3. D1, from S1
    have s2_3 : ∀ i : ℤ, i ∈ Finset.Icc 1 (m + m) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ) := by parley_set_side
    -- 2.4. calculation
    have s2_4 : m < m := by parley_count_after (by
      calc m = (((Set.Icc (1 : ℤ) (m + m) : Set ℤ) \ c).ncard : ℤ) := by parley_set_side
        _ < (((Set.Icc (1 : ℤ) (m + m) : Set ℤ) ∩ c).ncard : ℤ) := by first | linarith [(s2_3 (m + m) (by parley_set_side))] | (have h := (s2_3 (m + m) (by parley_set_side)); push_cast at h; linarith) | exact_mod_cast (s2_3 (m + m) (by parley_set_side)) | (have h := (s2_3 (m + m) (by parley_set_side)); parley_set_side)
        _ = m := by parley_set_side)
    -- 2.5. inequalities
    have s2_5 : ¬ m < m := by parley_set_side
    all_goals parley_set_side
  -- 3. mun:set-builder-empty X := O, from D2, D3, 2
  have s3 : {c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m + m) : Set ℤ) | (d.ncard : ℤ) = m} | ∀ i : ℤ, i ∈ Finset.Icc 1 (m + m) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)} = ∅ := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.mun_set_builder_empty (P := (fun c : Set ℤ => ∀ i : ℤ, i ∈ Finset.Icc 1 (m + m) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ))) (X := {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m + m) : Set ℤ) | (d.ncard : ℤ) = m}))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.mun_set_builder_empty (P := (fun c : Set ℤ => ∀ i : ℤ, i ∈ Finset.Icc 1 (m + m) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ))) (X := {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m + m) : Set ℤ) | (d.ncard : ℤ) = m}))).mpr (by parley_set_side); parley_set_side)
  all_goals exact s3

end Parley.Proofs.Wiedijk.Ballot.TieAtTheEnd
