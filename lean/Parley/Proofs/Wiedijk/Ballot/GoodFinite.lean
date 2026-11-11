module

public import SetTactics
public import Tactics
public import WholeTactics
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
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.SetNotationForOrder
public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Sets
public import Parley.Items.Stdlib.Sums

/-! Written from proofs/wiedijk/ballot.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.Ballot.GoodFinite

theorem good_finite (m : ℤ) (hH1 : 0 ≤ m) (n : ℤ) (hH2 : 0 ≤ n) :
    {c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m + n) : Set ℤ) | (d.ncard : ℤ) = m} | ∀ i : ℤ, i ∈ Finset.Icc 1 (m + n) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)}.Finite := by
  -- 1. mun:range-finite a := 1, b := m + n
  have s1 : (Set.Icc (1 : ℤ) (m + n) : Set ℤ).Finite := by exact (Parley.Items.Stdlib.Sums.mun_range_finite (a := (1 : ℤ)) (b := m + n))
  -- 2. proof
  have s2 : ∀ c ∈ {c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m + n) : Set ℤ) | (d.ncard : ℤ) = m} | ∀ i : ℤ, i ∈ Finset.Icc 1 (m + n) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)}, c ⊆ (Set.Icc (1 : ℤ) (m + n) : Set ℤ) := by
    intro c hK1
    -- 2.1. def:set-builder u := c, from D2, K1
    have s2_1 : c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m + n) : Set ℤ) | (d.ncard : ℤ) = m} := by exact (((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun c : Set ℤ => ∀ i : ℤ, i ∈ Finset.Icc 1 (m + n) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ))) (X := {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m + n) : Set ℤ) | (d.ncard : ℤ) = m}) (u := c))).mp (by parley_set_side)).1
    -- 2.2. def:part-builder u := c, from 2.1
    exact (((Parley.Items.Stdlib.Sets.def_part_builder (P := (fun d : Set ℤ => (d.ncard : ℤ) = m)) (X := (Set.Icc (1 : ℤ) (m + n) : Set ℤ)) (u := c))).mp (by parley_set_side)).1
  -- 3. mun:parts-finite A := {1, …, m + n}, K := G(m, n), from 1, 2
  exact (Parley.Items.Stdlib.Counting.mun_parts_finite (A := (Set.Icc (1 : ℤ) (m + n) : Set ℤ)) (K := {c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m + n) : Set ℤ) | (d.ncard : ℤ) = m} | ∀ i : ℤ, i ∈ Finset.Icc 1 (m + n) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)}) s1 (by parley_whole_side))

end Parley.Proofs.Wiedijk.Ballot.GoodFinite
