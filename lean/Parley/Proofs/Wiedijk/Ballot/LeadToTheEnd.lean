module

public import SetTactics
public import Tactics
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.SetNotationForOrder
public import Parley.Items.Proofs.Wiedijk.Ballot
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Reasoning
public import Parley.Items.Stdlib.Sums
public import Parley.Proofs.Wiedijk.Ballot.LastPlace

/-! Written from proofs/wiedijk/ballot.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.Ballot.LeadToTheEnd

theorem lead_to_the_end (m : ℤ) (hH1 : 0 ≤ m) (n : ℤ) (hH2 : 0 ≤ n) (c : Set ℤ) (hH3 : c ⊆ (Set.Icc (1 : ℤ) (m + n) : Set ℤ)) (hH4 : n < m) (hH5 : (c.ncard : ℤ) = m) (hH6 : ∀ i : ℤ, i ∈ Finset.Icc 1 (m + n - 1) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)) :
    (∀ i : ℤ, i ∈ Finset.Icc 1 (m + n) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ)) := by
  -- 1. D1, from H6
  have s1 : ∀ i : ℤ, i ∈ Finset.Icc 1 (m + n - 1) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ) := by parley_set_side
  -- 2. proof
  have s2 : ∀ i : ℤ, i ∈ Finset.Icc 1 (m + n) → (((Set.Icc (1 : ℤ) i : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).ncard : ℤ) := by
    intro i hK1
    try push_cast at hK1
    try have hK1_bounds := Finset.mem_Icc.mp hK1
    -- 2.1. axi:excluded-middle P := i = m + n
    have s2_1 : i = m + n ∨ i ≠ m + n := by exact (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := i = m + n))
    -- 2.2. cases, from 2.1
    rcases s2_1 with hC1 | hC2
    · skip
      -- 2.2.1. thm:last-place, from H3, H5
      have s2_2_1a : (((Set.Icc (1 : ℤ) (m + n) : Set ℤ) \ c).ncard : ℤ) = n := by exact (Parley.Proofs.Wiedijk.Ballot.LastPlace.last_place (m := m) hH1 (n := n) hH2 (c := c) hH3 hH5).1
      have s2_2_1b : (((Set.Icc (1 : ℤ) (m + n) : Set ℤ) ∩ c).ncard : ℤ) = m := by exact (Parley.Proofs.Wiedijk.Ballot.LastPlace.last_place (m := m) hH1 (n := n) hH2 (c := c) hH3 hH5).2
      -- 2.2.2. calculation
      have s2_2_2 : (((Set.Icc (1 : ℤ) (m + n) : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) (m + n) : Set ℤ) ∩ c).ncard : ℤ) := by parley_count_after (by
        calc (((Set.Icc (1 : ℤ) (m + n) : Set ℤ) \ c).ncard : ℤ) = n := by parley_set_side
          _ < m := by exact hH4
          _ = (((Set.Icc (1 : ℤ) (m + n) : Set ℤ) ∩ c).ncard : ℤ) := by parley_set_side)
      -- 2.2.3. substitute i = m + n (C1) into line 2.2.2
      (have h := Eq.subst (motive := (fun t : ℤ => (((Set.Icc (1 : ℤ) t : Set ℤ) \ c).ncard : ℤ) < (((Set.Icc (1 : ℤ) t : Set ℤ) ∩ c).ncard : ℤ))) hC1.symm s2_2_2; push_cast at h ⊢; all_goals exact_mod_cast h)
    · skip
      -- 2.2.4. mun:range-bounds a := 1, b := m + n, k := i, from K1
      have s2_2_4a : 1 ≤ i := by exact (Parley.Items.Stdlib.Sums.mun_range_bounds_1 (a := (1 : ℤ)) (b := m + n) (k := i) hK1)
      have s2_2_4b : i ≤ m + n := by exact (Parley.Items.Stdlib.Sums.mun_range_bounds_2 (a := (1 : ℤ)) (b := m + n) (k := i) hK1)
      -- 2.2.5. inequalities, from C2, 2.2.4
      have s2_2_5 : i < m + n := Or.elim (Ne.lt_or_gt hC2) (fun h1 => by linarith only [s2_2_4b, h1]) (fun h1 => by linarith only [s2_2_4b, h1])
      -- 2.2.6. mun:integer-step m := i, n := m + n, from 2.2.5
      have s2_2_6 : i + 1 ≤ m + n := by exact (Parley.Items.Stdlib.Numbers.mun_integer_step (m := i) (n := m + n) s2_2_5)
      -- 2.2.7. inequalities, from 2.2.6
      have s2_2_7 : i ≤ m + n - 1 := by linarith only [s2_2_6]
      -- 2.2.8. def:range-between k := i, a := 1, b := (m + n) − 1, from 2.2.4, 2.2.7
      have s2_2_8 : i ∈ Finset.Icc (1 : ℤ) (m + n - 1) := ((Parley.Items.Stdlib.Sums.def_range_between (k := i) (a := (1 : ℤ)) (b := m + n - 1))).mpr ⟨s2_2_4a, s2_2_7⟩
      -- 2.2.9. instantiate i := i in line 1, from 2.2.8
      exact (s1 i s2_2_8)
  -- 3. D1, from 2
  parley_set_side

end Parley.Proofs.Wiedijk.Ballot.LeadToTheEnd
