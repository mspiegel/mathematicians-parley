module

public import Counting
public import Functions
public import Batteries.Util.ExtendedBinder
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Reasoning
public import Parley.Proofs.Wiedijk.Ballot.BallotRecurrence
public import Parley.Proofs.Wiedijk.Ballot.GoodFinite
public import Parley.Proofs.Wiedijk.Ballot.NoVotesForB
public import Parley.Proofs.Wiedijk.Ballot.TieCount

/-! Written from proofs/wiedijk/ballot.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.Ballot.BallotCount

theorem ballot_count (a : ℤ) (hH1 : 0 ≤ a) (b : ℤ) (hH2 : 0 ≤ b) (hH3 : b ≤ a) :
    ({c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (a + b) : Set ℤ) | (d.ncard : ℤ) = a} | ∀ i : ℤ, i ∈ Finset.Icc 1 (a + b) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)}.ncard : ℤ) * (a + b) = (a - b) * (LeanBridges.Counting.choose (a + b) a : ℤ) := by
  -- 1. induction on k starting at 0
  have s1 : ∀ k : ℤ, 0 ≤ k → (∀ m : ℤ, 0 ≤ m → (∀ n : ℤ, 0 ≤ n → m + n = k ∧ n ≤ m → ({c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m + n) : Set ℤ) | (d.ncard : ℤ) = m} | ∀ i : ℤ, i ∈ Finset.Icc 1 (m + n) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)}.ncard : ℤ) * (m + n) = (m - n) * (LeanBridges.Counting.choose (m + n) m : ℤ))) := by
    intro k h_k
    replace h_k : 0 ≤ k := by omega
    induction k, h_k using LeanBridges.Functions.le_induction with
    | base =>
      intro m hK1
      intro n hK2
      intro hC1
      -- 1.1. restate C1
      have s1_1 : m + n = 0 := by exact hC1.1
      -- 1.2. inequalities, from K2
      have s1_2 : m ≤ m + n := by linarith only [hK2]
      -- 1.3. inequalities, from K1
      have s1_3 : n ≤ m + n := by linarith only [hK1]
      -- 1.4. transitivity, from 1.2, 1.1
      have s1_4 : m ≤ 0 := by exact LE.le.trans_eq s1_2 s1_1
      -- 1.5. transitivity, from 1.3, 1.1
      have s1_5 : n ≤ 0 := by exact LE.le.trans_eq s1_3 s1_1
      -- 1.6. inequalities, from K1
      have s1_6 : 0 ≤ m := by linarith only [hK1]
      -- 1.7. inequalities, from K2
      have s1_7 : 0 ≤ n := by linarith only [hK2]
      -- 1.8. antisymmetry, from 1.4, 1.6
      have s1_8 : m = 0 := le_antisymm s1_4 s1_6
      -- 1.9. antisymmetry, from 1.5, 1.7
      have s1_9 : n = 0 := le_antisymm s1_5 s1_7
      -- 1.10. algebra, from 1.8, 1.9
      have s1_10 : m - n = 0 := by linear_combination s1_8 + (-1) * s1_9
      -- 1.11. thm:good-finite
      have s1_11 : {c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m + n) : Set ℤ) | (d.ncard : ℤ) = m} | ∀ i : ℤ, i ∈ Finset.Icc 1 (m + n) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)}.Finite := by exact (Parley.Proofs.Wiedijk.Ballot.GoodFinite.good_finite (m := m) hK1 (n := n) hK2)
      -- 1.12. mun:card-nat0 X := G(m, n), from 1.11
      have s1_12 : 0 ≤ ({c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m + n) : Set ℤ) | (d.ncard : ℤ) = m} | ∀ i : ℤ, i ∈ Finset.Icc 1 (m + n) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)}.ncard : ℤ) := by exact (Parley.Items.Stdlib.Counting.mun_card_nat0 (X := {c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m + n) : Set ℤ) | (d.ncard : ℤ) = m} | ∀ i : ℤ, i ∈ Finset.Icc 1 (m + n) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)}) s1_11)
      -- 1.13. calculation
      calc ({c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m + n) : Set ℤ) | (d.ncard : ℤ) = m} | ∀ i : ℤ, i ∈ Finset.Icc 1 (m + n) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)}.ncard : ℤ) * (m + n) = 0 := by linear_combination (({c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m + n) : Set ℤ) | (d.ncard : ℤ) = m} | ∀ i : ℤ, i ∈ Finset.Icc 1 (m + n) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)}.ncard : ℤ)) * s1_1
        _ = (m - n) * (LeanBridges.Counting.choose (m + n) m : ℤ) := by linear_combination (-(LeanBridges.Counting.choose (m + n) m : ℤ)) * s1_10
    | succ k hK3 hIH =>
      intro m hK4
      intro n hK5
      intro hC2
      -- 1.14. mun:le-cases x := n, y := m, from C2
      have s1_14 : n < m ∨ n = m := by exact ((Parley.Items.Stdlib.Numbers.mun_le_cases (x := n) (y := m))).mp hC2.2
      -- 1.15. inequalities, from K5
      have s1_15 : 0 ≤ n := by linarith only [hK5]
      -- 1.16. cases, from 1.14
      rcases s1_14 with hC3 | hC6
      · skip
        -- 1.16.1. transitivity, from 1.15, C3
        have s1_16_1 : 0 < m := by exact lt_of_le_of_lt s1_15 hC3
        -- 1.16.2. mun:pos-int-nat, from 1.16.1
        have s1_16_2 : 0 < m := by exact (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := m) s1_16_1)
        -- 1.16.3. axi:excluded-middle P := n = 0
        have s1_16_3 : n = 0 ∨ n ≠ 0 := by exact (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := n = 0))
        -- 1.16.4. cases, from 1.16.3
        rcases s1_16_3 with hC4 | hC5
        · skip
          -- 1.16.4.1. thm:no-votes-for-b, from 1.16.2
          have s1_16_4_1 : ({c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m + 0) : Set ℤ) | (d.ncard : ℤ) = m} | ∀ i : ℤ, i ∈ Finset.Icc 1 (m + 0) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)}.ncard : ℤ) = 1 := by exact (Parley.Proofs.Wiedijk.Ballot.NoVotesForB.no_votes_for_b (m := m) s1_16_2)
          -- 1.16.4.2. substitute n = 0 (C4) into line 1.16.4.1
          have s1_16_4_2 : ({c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m + n) : Set ℤ) | (d.ncard : ℤ) = m} | ∀ i : ℤ, i ∈ Finset.Icc 1 (m + n) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)}.ncard : ℤ) = 1 := Eq.subst (motive := (fun t : ℤ => ({c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m + t) : Set ℤ) | (d.ncard : ℤ) = m} | ∀ i : ℤ, i ∈ Finset.Icc 1 (m + t) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)}.ncard : ℤ) = 1)) hC4.symm s1_16_4_1
          -- 1.16.4.3. calculation
          have s1_16_4_3 : (LeanBridges.Counting.choose (m + n) m : ℤ) = 1 := by
            calc (LeanBridges.Counting.choose (m + n) m : ℤ) = (LeanBridges.Counting.choose m m : ℤ) := by (have h := congrArg (fun t : ℤ => (LeanBridges.Counting.choose (m + t) m : ℤ)) hC4; push_cast [add_zero] at h ⊢; exact_mod_cast h)
              _ = 1 := by exact (Parley.Items.Stdlib.Counting.mun_binomial_all (n := m) hK4)
          -- 1.16.4.4. calculation
          calc ({c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m + n) : Set ℤ) | (d.ncard : ℤ) = m} | ∀ i : ℤ, i ∈ Finset.Icc 1 (m + n) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)}.ncard : ℤ) * (m + n) = m + n := by
                have e_nat : {c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m + n) : Set ℤ) | (d.ncard : ℤ) = m} | ∀ i : ℤ, i ∈ Finset.Icc 1 (m + n) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)}.ncard = 1 := by exact_mod_cast s1_16_4_2
                have e_w : ({c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m + n) : Set ℤ) | (d.ncard : ℤ) = m} | ∀ i : ℤ, i ∈ Finset.Icc 1 (m + n) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)}.ncard : ℤ) = 1 := by have h := congrArg (fun x : ℕ => (x : ℤ)) e_nat; push_cast at h ⊢; linear_combination h
                (have h := congrArg (fun t : ℤ => t * (m + n)) e_w; push_cast [one_mul] at h ⊢; exact_mod_cast h)
            _ = m - n := by linear_combination (2) * hC4
            _ = (m - n) * (LeanBridges.Counting.choose (m + n) m : ℤ) := by linear_combination (-m + n) * s1_16_4_3
        · skip
          -- 1.16.4.5. mun:nat0-nonzero m := n, from C5
          have s1_16_4_5 : 0 < n := by exact (Parley.Items.Stdlib.Numbers.mun_nat0_nonzero (m := n) hK5 hC5)
          -- 1.16.4.6. mun:nat-minus-one n := m, from 1.16.2
          have s1_16_4_6 : 0 ≤ m - 1 := by exact (Parley.Items.Stdlib.Numbers.mun_nat_minus_one (n := m) s1_16_2)
          -- 1.16.4.7. mun:nat-minus-one, from 1.16.4.5
          have s1_16_4_7 : 0 ≤ n - 1 := by exact (Parley.Items.Stdlib.Numbers.mun_nat_minus_one (n := n) s1_16_4_5)
          -- 1.16.4.8. algebra, from C2
          have s1_16_4_8 : m - 1 + n = k := by linear_combination hC2.1
          -- 1.16.4.9. mun:integer-step m := n, n := m, from C3
          have s1_16_4_9 : n + 1 ≤ m := by exact (Parley.Items.Stdlib.Numbers.mun_integer_step (m := n) (n := m) hC3)
          -- 1.16.4.10. inequalities
          have s1_16_4_10 : n ≤ m - 1 := by linarith only [s1_16_4_9]
          -- 1.16.4.11. instantiate m := m − 1, n := n in IH, from 1.16.4.6, 1.16.4.8, 1.16.4.10
          have s1_16_4_11 : ({c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m - 1 + n) : Set ℤ) | (d.ncard : ℤ) = m - 1} | ∀ i : ℤ, i ∈ Finset.Icc 1 (m - 1 + n) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)}.ncard : ℤ) * (m - 1 + n) = (m - 1 - n) * (LeanBridges.Counting.choose (m - 1 + n) (m - 1) : ℤ) := by exact (hIH (m - 1) s1_16_4_6 n hK5 ⟨s1_16_4_8, s1_16_4_10⟩)
          -- 1.16.4.12. algebra, from C2
          have s1_16_4_12 : m + (n - 1) = k := by linear_combination hC2.1
          -- 1.16.4.13. inequalities
          have s1_16_4_13 : n - 1 ≤ n := by linarith
          -- 1.16.4.14. inequalities
          have s1_16_4_14 : n ≤ m := by linarith only [hC3]
          -- 1.16.4.15. transitivity, from 1.16.4.13, 1.16.4.14
          have s1_16_4_15 : n - 1 ≤ m := by exact le_trans s1_16_4_13 s1_16_4_14
          -- 1.16.4.16. instantiate m := m, n := n − 1 in IH, from 1.16.4.7, 1.16.4.12, 1.16.4.15
          have s1_16_4_16 : ({c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m + (n - 1)) : Set ℤ) | (d.ncard : ℤ) = m} | ∀ i : ℤ, i ∈ Finset.Icc 1 (m + (n - 1)) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)}.ncard : ℤ) * (m + (n - 1)) = (m - (n - 1)) * (LeanBridges.Counting.choose (m + (n - 1)) m : ℤ) := by exact (hIH m hK4 (n - 1) s1_16_4_7 ⟨s1_16_4_12, s1_16_4_15⟩)
          -- 1.16.4.17. thm:ballot-recurrence, from C3, 1.16.2, 1.16.4.5, 1.16.4.6, 1.16.4.7, 1.16.4.11, 1.16.4.16
          exact (Parley.Proofs.Wiedijk.Ballot.BallotRecurrence.ballot_recurrence (m := m) s1_16_2 (n := n) s1_16_4_5 hC3 s1_16_4_11 s1_16_4_16)
      · skip
        -- 1.16.5. thm:tie-count, from K4
        have s1_16_5 : ({c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m + m) : Set ℤ) | (d.ncard : ℤ) = m} | ∀ i : ℤ, i ∈ Finset.Icc 1 (m + m) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)}.ncard : ℤ) * (m + m) = (m - m) * (LeanBridges.Counting.choose (m + m) m : ℤ) := by exact (Parley.Proofs.Wiedijk.Ballot.TieCount.tie_count (m := m) hK4)
        -- 1.16.6. substitute n = m (C6) into line 1.16.5
        exact Eq.subst (motive := (fun t : ℤ => ({c ∈ {d ∈ 𝒫 (Set.Icc (1 : ℤ) (m + t) : Set ℤ) | (d.ncard : ℤ) = m} | ∀ i : ℤ, i ∈ Finset.Icc 1 (m + t) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)}.ncard : ℤ) * (m + t) = (m - t) * (LeanBridges.Counting.choose (m + t) m : ℤ))) hC6.symm s1_16_5
  -- 2. instantiate k := a + b, m := a, n := b in line 1, from H3
  exact (s1 (a + b) (add_nonneg (hH1) (hH2)) a hH1 b hH2 ⟨rfl, hH3⟩)

end Parley.Proofs.Wiedijk.Ballot.BallotCount
