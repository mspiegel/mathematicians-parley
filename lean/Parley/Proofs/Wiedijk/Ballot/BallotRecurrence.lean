module

public import AlgebraTactics
public import Counting
public import FactorialTactics
public import InstanceTactics
public import NormTactics
public import OrderTactics
public import SetTactics
public import SubstTactics
public import Tactics
public import Batteries.Util.ExtendedBinder
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Rat.Init
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Set
public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Sets
public import Parley.Items.Stdlib.Sums
public import Parley.Proofs.Wiedijk.Ballot.AddLastPlace
public import Parley.Proofs.Wiedijk.Ballot.GoodFinite
public import Parley.Proofs.Wiedijk.Ballot.LastVoteForA
public import Parley.Proofs.Wiedijk.Ballot.LastVoteForB

/-! Written from proofs/wiedijk/ballot.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.Ballot.BallotRecurrence

set_option maxHeartbeats 800000 in
theorem ballot_recurrence (m : ℤ) (hH1 : 0 < m) (n : ℤ) (hH2 : 0 < n) (hH3 : n < m) (hH4 : ({c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m - 1 + n) : Set ℤ) | (d.ncard : ℤ) = m - 1} | ∀ i : ℤ, i ∈ Finset.Icc 1 (m - 1 + n) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)}.ncard : ℤ) * (m - 1 + n) = (m - 1 - n) * (LeanBridges.Counting.choose (m - 1 + n) (m - 1) : ℤ)) (hH5 : ({c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m + (n - 1)) : Set ℤ) | (d.ncard : ℤ) = m} | ∀ i : ℤ, i ∈ Finset.Icc 1 (m + (n - 1)) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)}.ncard : ℤ) * (m + (n - 1)) = (m - (n - 1)) * (LeanBridges.Counting.choose (m + (n - 1)) m : ℤ)) :
    ({c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m + n) : Set ℤ) | (d.ncard : ℤ) = m} | ∀ i : ℤ, i ∈ Finset.Icc 1 (m + n) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)}.ncard : ℤ) * (m + n) = (m - n) * (LeanBridges.Counting.choose (m + n) m : ℤ) := by
  set U : Set (Set ℤ) := {c ∈ {c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m + n) : Set ℤ) | (d.ncard : ℤ) = m} | ∀ i : ℤ, i ∈ Finset.Icc 1 (m + n) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)} | m + n ∈ c} with hD3
  have hD3_finite : U.Finite := by rw [hD3]; exact ((((Set.finite_Icc _ _).powerset).subset (fun _ h => h.1)).subset (fun _ h => h.1)).subset (fun _ h => h.1)
  set V : Set (Set ℤ) := {c ∈ {c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m + n) : Set ℤ) | (d.ncard : ℤ) = m} | ∀ i : ℤ, i ∈ Finset.Icc 1 (m + n) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)} | ¬ m + n ∈ c} with hD4
  have hD4_finite : V.Finite := by rw [hD4]; exact ((((Set.finite_Icc _ _).powerset).subset (fun _ h => h.1)).subset (fun _ h => h.1)).subset (fun _ h => h.1)
  -- 1. mun:nat-minus-one n := m
  have s1 : 0 ≤ m - 1 := by exact (Parley.Items.Stdlib.Numbers.mun_nat_minus_one (n := m) (by parley_set_side))
  -- 2. mun:nat-minus-one
  have s2 : 0 ≤ n - 1 := by exact (Parley.Items.Stdlib.Numbers.mun_nat_minus_one (n := n) (by parley_set_side))
  -- 3. mun:set-builder-split X := G(m, n), from D3, D4
  have s3 : {c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m + n) : Set ℤ) | (d.ncard : ℤ) = m} | ∀ i : ℤ, i ∈ Finset.Icc 1 (m + n) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)} = U ∪ V := by
    try simp only [hD3, hD4] at *
    try push_cast at *
    exact (Parley.Items.Stdlib.Sets.mun_set_builder_split (P := (fun c : Set ℤ => m + n ∈ c)) (X := {c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m + n) : Set ℤ) | (d.ncard : ℤ) = m} | ∀ i : ℤ, i ∈ Finset.Icc 1 (m + n) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)}))
  -- 4. mun:set-builder-split-disjoint X := G(m, n), from D3, D4
  have s4 : U ∩ V = ∅ := by
    try simp only [hD3, hD4] at *
    try push_cast at *
    exact (Parley.Items.Stdlib.Sets.mun_set_builder_split_disjoint (P := (fun c : Set ℤ => m + n ∈ c)) (X := {c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m + n) : Set ℤ) | (d.ncard : ℤ) = m} | ∀ i : ℤ, i ∈ Finset.Icc 1 (m + n) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)}))
  -- 5. thm:last-vote-for-a, from D3, H3, 1
  have s5 : U = (fun T : Set ℤ => T ∪ ({m + n} : Set ℤ)) '' {c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m - 1 + n) : Set ℤ) | (d.ncard : ℤ) = m - 1} | ∀ i : ℤ, i ∈ Finset.Icc 1 (m - 1 + n) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)} := by
    try simp only [hD3] at *
    try push_cast at *
    exact (Parley.Proofs.Wiedijk.Ballot.LastVoteForA.last_vote_for_a (m := m) (by parley_set_side) (n := n) (by parley_set_side) hH3)
  -- 6. thm:last-vote-for-b, from D4, H3, 2
  have s6 : V = {c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m + (n - 1)) : Set ℤ) | (d.ncard : ℤ) = m} | ∀ i : ℤ, i ∈ Finset.Icc 1 (m + (n - 1)) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)} := by
    try simp only [hD4] at *
    try push_cast at *
    exact (Parley.Proofs.Wiedijk.Ballot.LastVoteForB.last_vote_for_b (m := m) (by parley_set_side) (n := n) (by parley_set_side) hH3)
  -- 7. thm:add-last-place, from 1
  have s7 : ∃ g : Set ℤ → Set ℤ, Set.BijOn g {c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m - 1 + n) : Set ℤ) | (d.ncard : ℤ) = m - 1} | ∀ i : ℤ, i ∈ Finset.Icc 1 (m - 1 + n) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)} ((fun T : Set ℤ => T ∪ ({m + n} : Set ℤ)) '' {c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m - 1 + n) : Set ℤ) | (d.ncard : ℤ) = m - 1} | ∀ i : ℤ, i ∈ Finset.Icc 1 (m - 1 + n) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)}) := by exact (Parley.Proofs.Wiedijk.Ballot.AddLastPlace.add_last_place (m := m) (by parley_set_side) (n := n) (by parley_set_side))
  -- 8. thm:good-finite m := m − 1, from 1
  have s8 : {c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m - 1 + n) : Set ℤ) | (d.ncard : ℤ) = m - 1} | ∀ i : ℤ, i ∈ Finset.Icc 1 (m - 1 + n) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)}.Finite := by exact (Parley.Proofs.Wiedijk.Ballot.GoodFinite.good_finite (m := m - 1) (by parley_set_side) (n := n) (by parley_set_side))
  -- 9. thm:good-finite n := n − 1, from 2
  have s9 : {c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m + (n - 1)) : Set ℤ) | (d.ncard : ℤ) = m} | ∀ i : ℤ, i ∈ Finset.Icc 1 (m + (n - 1)) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)}.Finite := by exact (Parley.Proofs.Wiedijk.Ballot.GoodFinite.good_finite (m := m) (by parley_set_side) (n := n - 1) (by parley_set_side))
  -- 10. calculation
  have s10 : (U.ncard : ℤ) = ({c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m - 1 + n) : Set ℤ) | (d.ncard : ℤ) = m - 1} | ∀ i : ℤ, i ∈ Finset.Icc 1 (m - 1 + n) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)}.ncard : ℤ) := by parley_count_after (by
    calc (U.ncard : ℤ) = (((fun T : Set ℤ => T ∪ ({m + n} : Set ℤ)) '' {c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m - 1 + n) : Set ℤ) | (d.ncard : ℤ) = m - 1} | ∀ i : ℤ, i ∈ Finset.Icc 1 (m - 1 + n) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)}).ncard : ℤ) := by parley_subst s5
      _ = ({c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m - 1 + n) : Set ℤ) | (d.ncard : ℤ) = m - 1} | ∀ i : ℤ, i ∈ Finset.Icc 1 (m - 1 + n) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)}.ncard : ℤ) := by (have h := (Parley.Items.Stdlib.Counting.mun_card_equal (X := {c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m - 1 + n) : Set ℤ) | (d.ncard : ℤ) = m - 1} | ∀ i : ℤ, i ∈ Finset.Icc 1 (m - 1 + n) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)}) (Y := (fun T : Set ℤ => T ∪ ({m + n} : Set ℤ)) '' {c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m - 1 + n) : Set ℤ) | (d.ncard : ℤ) = m - 1} | ∀ i : ℤ, i ∈ Finset.Icc 1 (m - 1 + n) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)}) (by parley_set_side) (by parley_set_side)); simp only [← Set.Finite.cast_ncard_eq (show ((fun T : Set ℤ => T ∪ {m + n}) '' {c ∈ {d ∈ 𝒫 (Set.Icc 1 (m - 1 + n)) | (d.ncard : ℤ) = m - 1} | ∀ i : ℤ, i ∈ Finset.Icc 1 (m - 1 + n) → ((Set.Icc 1 i \ c).ncard : ℤ) < ((Set.Icc 1 i ∩ c).ncard : ℤ)} : Set (Set ℤ)).Finite by parley_finite)] at h ⊢; exact_mod_cast h.symm))
  -- 11. substitute V = G(m, n − 1) (line 6)
  have s11 : (V.ncard : ℤ) = ({c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m + (n - 1)) : Set ℤ) | (d.ncard : ℤ) = m} | ∀ i : ℤ, i ∈ Finset.Icc 1 (m + (n - 1)) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)}.ncard : ℤ) := by parley_subst s6
  -- 12. mun:card-nat0 X := G(m − 1, n), from 8
  have s12 : 0 ≤ ({c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m - 1 + n) : Set ℤ) | (d.ncard : ℤ) = m - 1} | ∀ i : ℤ, i ∈ Finset.Icc 1 (m - 1 + n) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)}.ncard : ℤ) := by exact (Parley.Items.Stdlib.Counting.mun_card_nat0 (X := {c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m - 1 + n) : Set ℤ) | (d.ncard : ℤ) = m - 1} | ∀ i : ℤ, i ∈ Finset.Icc 1 (m - 1 + n) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)}) (by parley_set_side))
  -- 13. mun:card-nat0 X := G(m, n − 1), from 9
  have s13 : 0 ≤ ({c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m + (n - 1)) : Set ℤ) | (d.ncard : ℤ) = m} | ∀ i : ℤ, i ∈ Finset.Icc 1 (m + (n - 1)) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)}.ncard : ℤ) := by exact (Parley.Items.Stdlib.Counting.mun_card_nat0 (X := {c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m + (n - 1)) : Set ℤ) | (d.ncard : ℤ) = m} | ∀ i : ℤ, i ∈ Finset.Icc 1 (m + (n - 1)) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)}) (by parley_set_side))
  -- 14. mun:card-disjoint-union X := U, Y := V, m := |G(m − 1, n)|, n := |G(m, n − 1)|, from 4, 10, 11, 12, 13
  have s14 : ((U ∪ V).ncard : ℤ) = ({c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m - 1 + n) : Set ℤ) | (d.ncard : ℤ) = m - 1} | ∀ i : ℤ, i ∈ Finset.Icc 1 (m - 1 + n) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)}.ncard : ℤ) + ({c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m + (n - 1)) : Set ℤ) | (d.ncard : ℤ) = m} | ∀ i : ℤ, i ∈ Finset.Icc 1 (m + (n - 1)) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)}.ncard : ℤ) := by exact (Parley.Items.Stdlib.Counting.mun_card_disjoint_union (X := U) (Y := V) (m := ({c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m - 1 + n) : Set ℤ) | (d.ncard : ℤ) = m - 1} | ∀ i : ℤ, i ∈ Finset.Icc 1 (m - 1 + n) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)}.ncard : ℤ)) (by parley_set_side) (n := ({c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m + (n - 1)) : Set ℤ) | (d.ncard : ℤ) = m} | ∀ i : ℤ, i ∈ Finset.Icc 1 (m + (n - 1)) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)}.ncard : ℤ)) (by parley_set_side) (by parley_set_side) (by parley_set_side) (by parley_set_side))
  -- 15. substitute G(m, n) = U ∪ V (line 3) into line 14
  have s15 : ({c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m + n) : Set ℤ) | (d.ncard : ℤ) = m} | ∀ i : ℤ, i ∈ Finset.Icc 1 (m + n) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)}.ncard : ℤ) = ({c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m - 1 + n) : Set ℤ) | (d.ncard : ℤ) = m - 1} | ∀ i : ℤ, i ∈ Finset.Icc 1 (m - 1 + n) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)}.ncard : ℤ) + ({c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m + (n - 1)) : Set ℤ) | (d.ncard : ℤ) = m} | ∀ i : ℤ, i ∈ Finset.Icc 1 (m + (n - 1)) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)}.ncard : ℤ) := by parley_count_int; (parley_subst_at s3 s14)
  -- 16. thm:good-finite
  have s16 : {c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m + n) : Set ℤ) | (d.ncard : ℤ) = m} | ∀ i : ℤ, i ∈ Finset.Icc 1 (m + n) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)}.Finite := by exact (Parley.Proofs.Wiedijk.Ballot.GoodFinite.good_finite (m := m) (by parley_set_side) (n := n) (by parley_set_side))
  -- 17. mun:card-nat0 X := G(m, n), from 16
  have s17 : 0 ≤ ({c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m + n) : Set ℤ) | (d.ncard : ℤ) = m} | ∀ i : ℤ, i ∈ Finset.Icc 1 (m + n) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)}.ncard : ℤ) := by exact (Parley.Items.Stdlib.Counting.mun_card_nat0 (X := {c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m + n) : Set ℤ) | (d.ncard : ℤ) = m} | ∀ i : ℤ, i ∈ Finset.Icc 1 (m + n) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)}) (by parley_set_side))
  -- 18. algebra
  have s18 : m - 1 + n = m + (n - 1) := by parley_ring
  -- 19. substitute (m − 1) + n = m + (n − 1) (line 18) into H4
  have r846_1 : 0 ≤ m - 1 := by parley_set_side
  have s19 : ({c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m - 1 + n) : Set ℤ) | (d.ncard : ℤ) = m - 1} | ∀ i : ℤ, i ∈ Finset.Icc 1 (m - 1 + n) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)}.ncard : ℤ) * (m + (n - 1)) = (m - 1 - n) * (LeanBridges.Counting.choose (m + (n - 1)) (m - 1) : ℤ) := by parley_subst_at s18 hH4
  -- 20. inequalities, from H2
  have s20 : m - 1 ≤ m + (n - 1) := by parley_order
  -- 21. def:range0 k := m − 1, n := m + (n − 1), from 1, 2, 20
  have s21 : m - 1 ∈ Finset.Icc (0 : ℤ) (m + (n - 1)) := ((Parley.Items.Stdlib.Sums.def_range0 (k := m - 1) (n := m + (n - 1)) (by parley_set_side))).mpr (by parley_set_side)
  -- 22. thm:absorption n := m + (n − 1), k := m − 1, from 2, 21
  have s22 : (LeanBridges.Counting.choose (m + (n - 1) + 1) (m - 1 + 1) : ℚ) = (LeanBridges.Counting.choose (m + (n - 1)) (m - 1) : ℚ) * (((m : ℚ) + ((n : ℚ) - 1) + 1) / ((m : ℚ) - 1 + 1)) := by
    have hI : (LeanBridges.Counting.choose (m + (n - 1) + 1) (m - 1 + 1) : ℚ) = (LeanBridges.Counting.choose (m + (n - 1)) (m - 1) : ℚ) * (((m : ℚ) + ((n : ℚ) - 1) + 1) / ((m : ℚ) - 1 + 1)) := by parley_instance ((Parley.Items.Stdlib.Counting.thm_absorption (n := m + (n - 1)) (by parley_set_side) (k := m - 1) s21))
    exact hI
  -- 23. algebra
  have s23 : m + (n - 1) + 1 = m + n := by parley_ring
  -- 24. substitute (m + (n − 1)) + 1 = m + n (line 23) into line 22
  have s24 : (LeanBridges.Counting.choose (m + n) (m - 1 + 1) : ℚ) = (LeanBridges.Counting.choose (m + (n - 1)) (m - 1) : ℚ) * (((m : ℚ) + (n : ℚ)) / ((m : ℚ) - 1 + 1)) := by
    have s23_w : (m : ℚ) + ((n : ℚ) - 1) + 1 = (m : ℚ) + (n : ℚ) := by have h := congrArg (fun x : ℤ => (x : ℚ)) s23; push_cast at h; linear_combination (norm := parley_norm) h
    first | parley_subst_at s23_w s22 | parley_subst_at s23 s22
  -- 25. substitute
  have s25 : (LeanBridges.Counting.choose (m + n) m : ℚ) = (LeanBridges.Counting.choose (m + (n - 1)) (m - 1) : ℚ) * (((m : ℚ) + (n : ℚ)) / (m : ℚ)) := by
    have c1 : m - 1 + 1 = m := by parley_ring
    have c1_w : (m : ℚ) - 1 + 1 = (m : ℚ) := by have h := congrArg (fun x : ℤ => (x : ℚ)) c1; push_cast at h; linear_combination (norm := parley_norm) h
    have row1 : (LeanBridges.Counting.choose (m + n) m : ℚ) = (LeanBridges.Counting.choose (m + (n - 1)) (m - 1) : ℚ) * (((m : ℚ) + (n : ℚ)) / (m : ℚ)) := by first | parley_put_at c1_w s24 | parley_put_at c1 s24 | parley_subst_at c1_w s24 | parley_subst_at c1 s24
    exact row1
  -- 26. thm:pascal n := m + (n − 1), k := m, from 2
  have s26 : (LeanBridges.Counting.choose (m + (n - 1)) m : ℤ) + (LeanBridges.Counting.choose (m + (n - 1)) (m - 1) : ℤ) = (LeanBridges.Counting.choose (m + (n - 1) + 1) m : ℤ) := by exact (Parley.Items.Stdlib.Counting.thm_pascal (n := m + (n - 1)) (by parley_set_side) (k := m))
  -- 27. substitute (m + (n − 1)) + 1 = m + n (line 23) into line 26
  have s27 : (LeanBridges.Counting.choose (m + (n - 1)) m : ℤ) + (LeanBridges.Counting.choose (m + (n - 1)) (m - 1) : ℤ) = (LeanBridges.Counting.choose (m + n) m : ℤ) := by (have h := Eq.subst (motive := (fun t : ℤ => (LeanBridges.Counting.choose (m + (n - 1)) m : ℤ) + (LeanBridges.Counting.choose (m + (n - 1)) (m - 1) : ℤ) = (LeanBridges.Counting.choose t m : ℤ))) s23 s26; push_cast at h ⊢; all_goals exact_mod_cast h)
  -- 28. mun:binomial-nat0 n := m + (n − 1), k := m − 1, from 2
  have s28 : 0 ≤ (LeanBridges.Counting.choose (m + (n - 1)) (m - 1) : ℤ) := by exact (Parley.Items.Stdlib.Counting.mun_binomial_nat0 (n := m + (n - 1)) (by parley_set_side) (k := m - 1))
  -- 29. mun:binomial-nat0 n := m + (n − 1), k := m, from 2
  have s29 : 0 ≤ (LeanBridges.Counting.choose (m + (n - 1)) m : ℤ) := by exact (Parley.Items.Stdlib.Counting.mun_binomial_nat0 (n := m + (n - 1)) (by parley_set_side) (k := m))
  -- 30. algebra, from 25, 28
  have s30 : (LeanBridges.Counting.choose (m + (n - 1)) (m - 1) : ℤ) * (m + n) = m * (LeanBridges.Counting.choose (m + n) m : ℤ) := by qify at *; linear_combination (norm := parley_field) (-(m : ℚ)) * s25
  -- 31. algebra, from 27, 28, 29, 30
  have s31 : (LeanBridges.Counting.choose (m + (n - 1)) m : ℤ) * (m + n) = n * (LeanBridges.Counting.choose (m + n) m : ℤ) := by linear_combination (norm := parley_norm) (m + n) * s27 + (-1) * s30
  -- 32. algebra, from H5, 12, 13, 15, 19
  have r888_1 : 0 ≤ n - 1 := by parley_set_side
  have s32 : ({c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m + n) : Set ℤ) | (d.ncard : ℤ) = m} | ∀ i : ℤ, i ∈ Finset.Icc 1 (m + n) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)}.ncard : ℤ) * (m + (n - 1)) = (m - 1 - n) * (LeanBridges.Counting.choose (m + (n - 1)) (m - 1) : ℤ) + (m - (n - 1)) * (LeanBridges.Counting.choose (m + (n - 1)) m : ℤ) := by parley_count_int; (linear_combination (norm := parley_norm) hH5 + (m + n - 1) * s15 + s19)
  -- 33. algebra, from 28, 30
  have s33 : (m - 1 - n) * (LeanBridges.Counting.choose (m + (n - 1)) (m - 1) : ℤ) * (m + n) = (m - 1 - n) * m * (LeanBridges.Counting.choose (m + n) m : ℤ) := by linear_combination (norm := parley_norm) (m - n - 1) * s30
  -- 34. algebra, from 29, 31
  have s34 : (m - (n - 1)) * (LeanBridges.Counting.choose (m + (n - 1)) m : ℤ) * (m + n) = (m - (n - 1)) * n * (LeanBridges.Counting.choose (m + n) m : ℤ) := by linear_combination (norm := parley_norm) (m - n + 1) * s31
  -- 35. algebra, from 17, 28, 29, 32, 33, 34
  have s35 : ({c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m + n) : Set ℤ) | (d.ncard : ℤ) = m} | ∀ i : ℤ, i ∈ Finset.Icc 1 (m + n) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)}.ncard : ℤ) * (m + (n - 1)) * (m + n) = (m - 1 - n) * m * (LeanBridges.Counting.choose (m + n) m : ℤ) + (m - (n - 1)) * n * (LeanBridges.Counting.choose (m + n) m : ℤ) := by parley_count_int; (linear_combination (norm := parley_norm) (m + n) * s32 + s33 + s34)
  -- 36. inequalities, from H1, H2
  have s36 : 0 < m + (n - 1) := by parley_order
  -- 37. calculation
  have r904_1 : 0 ≠ m + (n - 1) := by parley_set_side
  parley_count_after (by
    try qify
    calc ({c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m + n) : Set ℤ) | (d.ncard : ℤ) = m} | ∀ i : ℤ, i ∈ Finset.Icc 1 (m + n) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)}.ncard : ℚ) * ((m : ℚ) + (n : ℚ)) = (((m : ℚ) - 1 - (n : ℚ)) * (m : ℚ) * (LeanBridges.Counting.choose (m + n) m : ℚ) + ((m : ℚ) - ((n : ℚ) - 1)) * (n : ℚ) * (LeanBridges.Counting.choose (m + n) m : ℚ)) / ((m : ℚ) + ((n : ℚ) - 1)) := by parley_count_int; exact (by
          have s35_w : ({c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m + n) : Set ℤ) | (d.ncard : ℤ) = m} | ∀ i : ℤ, i ∈ Finset.Icc 1 (m + n) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)}.ncard : ℚ) * ((m : ℚ) + ((n : ℚ) - 1)) * ((m : ℚ) + (n : ℚ)) = ((m : ℚ) - 1 - (n : ℚ)) * (m : ℚ) * (LeanBridges.Counting.choose (m + n) m : ℚ) + ((m : ℚ) - ((n : ℚ) - 1)) * (n : ℚ) * (LeanBridges.Counting.choose (m + n) m : ℚ) := by have h := congrArg (fun x : ℤ => (x : ℚ)) s35; push_cast at h; linear_combination (norm := parley_norm) h
          linear_combination (norm := parley_field) ((1) / (((m : ℚ) + (n : ℚ) - 1))) * s35_w)
      _ = ((m : ℚ) - (n : ℚ)) * (LeanBridges.Counting.choose (m + n) m : ℚ) := by parley_ring)

end Parley.Proofs.Wiedijk.Ballot.BallotRecurrence
