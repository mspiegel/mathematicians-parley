module

public import AlgebraTactics
public import Counting
public import FactorialTactics
public import NormTactics
public import SetTactics
public import SubstTactics
public import Tactics
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
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Reasoning
public import Parley.Proofs.Wiedijk.Ballot.GoodFinite
public import Parley.Proofs.Wiedijk.Ballot.TieAtTheEnd

/-! Written from proofs/wiedijk/ballot.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.Ballot.TieCount

theorem tie_count (m : ℤ) (hH1 : 0 ≤ m) :
    ({c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m + m) : Set ℤ) | (d.ncard : ℤ) = m} | ∀ i : ℤ, i ∈ Finset.Icc 1 (m + m) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)}.ncard : ℤ) * (m + m) = (m - m) * (LeanBridges.Counting.choose (m + m) m : ℤ) := by
  -- 1. axi:excluded-middle P := m = 0
  have s1 : m = 0 ∨ m ≠ 0 := by exact (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := m = 0))
  -- 2. cases, from 1
  rcases s1 with hC1 | hC2
  · skip
    -- 2.1. thm:good-finite n := m
    have s2_1 : {c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m + m) : Set ℤ) | (d.ncard : ℤ) = m} | ∀ i : ℤ, i ∈ Finset.Icc 1 (m + m) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)}.Finite := by exact (Parley.Proofs.Wiedijk.Ballot.GoodFinite.good_finite (m := m) hH1 (n := m) hH1)
    -- 2.2. mun:card-nat0 X := G(m, m), from 2.1
    have s2_2 : 0 ≤ ({c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m + m) : Set ℤ) | (d.ncard : ℤ) = m} | ∀ i : ℤ, i ∈ Finset.Icc 1 (m + m) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)}.ncard : ℤ) := by exact (Parley.Items.Stdlib.Counting.mun_card_nat0 (X := {c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m + m) : Set ℤ) | (d.ncard : ℤ) = m} | ∀ i : ℤ, i ∈ Finset.Icc 1 (m + m) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)}) (by parley_set_side))
    -- 2.3. calculation
    parley_count_after (by
      calc ({c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m + m) : Set ℤ) | (d.ncard : ℤ) = m} | ∀ i : ℤ, i ∈ Finset.Icc 1 (m + m) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)}.ncard : ℤ) * (m + m) = 0 := by parley_count_int; (linear_combination (norm := parley_norm) (2 * ({c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m + m) : Set ℤ) | (d.ncard : ℤ) = m} | ∀ i : ℤ, i ∈ Finset.Icc 1 (m + m) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)}.ncard : ℤ)) * hC1)
        _ = (m - m) * (LeanBridges.Counting.choose (m + m) m : ℤ) := by parley_ring)
  · skip
    -- 2.4. mun:nat0-nonzero, from C2
    have s2_4 : 0 < m := by exact (Parley.Items.Stdlib.Numbers.mun_nat0_nonzero (m := m) hH1 hC2)
    -- 2.5. thm:tie-at-the-end, from 2.4
    have s2_5 : {c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m + m) : Set ℤ) | (d.ncard : ℤ) = m} | ∀ i : ℤ, i ∈ Finset.Icc 1 (m + m) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)} = ∅ := by exact (Parley.Proofs.Wiedijk.Ballot.TieAtTheEnd.tie_at_the_end (m := m) s2_4)
    -- 2.6. calculation
    have s2_6 : ({c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m + m) : Set ℤ) | (d.ncard : ℤ) = m} | ∀ i : ℤ, i ∈ Finset.Icc 1 (m + m) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)}.ncard : ℤ) = 0 := by parley_count_after (by
      calc ({c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m + m) : Set ℤ) | (d.ncard : ℤ) = m} | ∀ i : ℤ, i ∈ Finset.Icc 1 (m + m) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)}.ncard : ℤ) = ((∅ : Set (Set ℤ)).ncard : ℤ) := by parley_subst s2_5
        _ = 0 := by exact Parley.Items.Stdlib.Counting.mun_card_empty)
    -- 2.7. calculation
    parley_count_after (by
      calc ({c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m + m) : Set ℤ) | (d.ncard : ℤ) = m} | ∀ i : ℤ, i ∈ Finset.Icc 1 (m + m) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)}.ncard : ℤ) * (m + m) = 0 := by parley_count_int; (linear_combination (norm := parley_norm) (2 * m) * s2_6)
        _ = (m - m) * (LeanBridges.Counting.choose (m + m) m : ℤ) := by parley_ring)

end Parley.Proofs.Wiedijk.Ballot.TieCount
