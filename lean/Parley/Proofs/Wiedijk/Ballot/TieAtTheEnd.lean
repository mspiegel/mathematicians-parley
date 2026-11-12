module

public import InstanceTactics
public import SetTactics
public import Tactics
public import Batteries.Util.ExtendedBinder
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Basic.Finite.Defs
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
  have s1 : m + m ∈ Finset.Icc (1 : ℤ) (m + m) := by exact (Parley.Items.Stdlib.Sums.mun_range_end (n := m + m) (add_pos (hH1) (hH1)))
  -- 2. proof
  have s2 : ∀ c ∈ O, ¬ (∀ i : ℤ, i ∈ Finset.Icc 1 (m + m) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)) := by
    intro c hK1
    intro hS1
    -- 2.1. def:part-builder u := c, from D3, K1
    have s2_1a : c ⊆ (Set.Icc (1 : ℤ) (m + m) : Set ℤ) := by
      try simp only [hD3] at ⊢
      try push_cast at ⊢
      exact (((Parley.Items.Stdlib.Sets.def_part_builder (P := (fun d : Set ℤ => (d.ncard : ℤ) = m)) (X := (Set.Icc (1 : ℤ) (m + m) : Set ℤ)) (u := c))).mp (by parley_set_side)).1
    have s2_1b : (c.ncard : ℤ) = m := by
      try simp only [hD3] at ⊢
      try push_cast at ⊢
      have hI : (c.ncard : ℤ) = m := by parley_instance ((((Parley.Items.Stdlib.Sets.def_part_builder (P := (fun d : Set ℤ => (d.ncard : ℤ) = m)) (X := (Set.Icc (1 : ℤ) (m + m) : Set ℤ)) (u := c))).mp (by parley_set_side)).2)
      exact hI
    -- 2.2. thm:last-place n := m, from 2.1
    have s2_2a : (((Set.Icc (1 : ℤ) (m + m) : Set ℤ) \ c).ncard : ℤ) = m := by exact (Parley.Proofs.Wiedijk.Ballot.LastPlace.last_place (m := m) (le_of_lt hH1) (n := m) (le_of_lt hH1) (c := c) s2_1a (by parley_set_side)).1
    have s2_2b : (((Set.Icc (1 : ℤ) (m + m) : Set ℤ) ∩ c).ncard : ℤ) = m := by exact (Parley.Proofs.Wiedijk.Ballot.LastPlace.last_place (m := m) (le_of_lt hH1) (n := m) (le_of_lt hH1) (c := c) s2_1a (by parley_set_side)).2
    -- 2.3. D1, from S1
    have s2_3 : ∀ i : ℤ, i ∈ Finset.Icc 1 (m + m) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ) := by parley_set_side
    -- 2.4. calculation
    have s2_4 : m < m := by parley_count_after (by
      calc m = (((Set.Icc (1 : ℤ) (m + m) : Set ℤ) \ c).ncard : ℤ) := by parley_set_side
        _ < (((Set.Icc (1 : ℤ) (m + m) : Set ℤ) ∩ c).ncard : ℤ) := by exact (s2_3 (m + m) s1)
        _ = m := by parley_set_side)
    -- 2.5. inequalities
    have s2_5 : ¬ m < m := by linarith
    exact s2_5 s2_4
  -- 3. mun:set-builder-empty X := O, from D2, D3, 2
  exact ((Parley.Items.Stdlib.Sets.mun_set_builder_empty (P := (fun c : Set ℤ => ∀ i : ℤ, i ∈ Finset.Icc 1 (m + m) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ))) (X := {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m + m) : Set ℤ) | (d.ncard : ℤ) = m}))).mpr (by parley_set_side)

end Parley.Proofs.Wiedijk.Ballot.TieAtTheEnd
