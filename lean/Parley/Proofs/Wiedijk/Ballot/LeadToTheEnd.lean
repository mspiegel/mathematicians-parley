module

public import OrderTactics
public import PowerTactics
public import SetTactics
public import SubstTactics
public import Tactics
public import Mathlib.Data.ENat.Defs
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.SetNotationForOrder
public import Parley.Items.Proofs.Wiedijk.Ballot
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Reasoning
public import Parley.Items.Stdlib.Sums
public import Parley.Proofs.Wiedijk.Ballot.LastPlace

/-! Written from proofs/wiedijk/ballot.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.Ballot.LeadToTheEnd

set_option maxHeartbeats 400000 in
theorem lead_to_the_end (m : ℤ) (hH1 : 0 ≤ m) (n : ℤ) (hH2 : 0 ≤ n) (c : Set ℤ) (hH3 : c ⊆ (Set.Icc (1 : ℤ) (m + n) : Set ℤ)) (hH4 : n < m) (hH5 : c.encard = ((m.toNat : ℕ) : ℕ∞)) (hH6 : ∀ i : ℤ, i ∈ Finset.Icc 1 (m + n - 1) → ((Set.Icc (1 : ℤ) i : Set ℤ) \ c).encard < ((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).encard) :
    (∀ i : ℤ, i ∈ Finset.Icc 1 (m + n) → ((Set.Icc (1 : ℤ) i : Set ℤ) \ c).encard < ((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).encard) := by
  -- 1. D1, from H6
  have s1 : ∀ i : ℤ, i ∈ Finset.Icc 1 (m + n - 1) → ((Set.Icc (1 : ℤ) i : Set ℤ) \ c).encard < ((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).encard := by parley_set_side
  -- 2. proof
  have s2 : ∀ i : ℤ, i ∈ Finset.Icc 1 (m + n) → ((Set.Icc (1 : ℤ) i : Set ℤ) \ c).encard < ((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).encard := by
    intro i hK1
    try push_cast at hK1
    try have hK1_bounds := Finset.mem_Icc.mp hK1
    -- 2.1. axi:excluded-middle P := i = m + n
    have s2_1 : i = m + n ∨ i ≠ m + n := by first | exact (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := i = m + n)) | exact ((Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := i = m + n))).symm | simpa using (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := i = m + n)) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := i = m + n)) | (have h := (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := i = m + n)); parley_set_side)
    -- 2.2. cases, from 2.1
    have s2_2 : ((Set.Icc (1 : ℤ) i : Set ℤ) \ c).encard < ((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).encard := by
      rcases s2_1 with hC1 | hC2
      · skip
        -- 2.2.1. thm:last-place, from H3, H5
        have s2_2_1a : ((Set.Icc (1 : ℤ) (m + n) : Set ℤ) \ c).encard = ((n.toNat : ℕ) : ℕ∞) := by first | linear_combination (norm := parley_norm) (Parley.Proofs.Wiedijk.Ballot.LastPlace.last_place (m := m) (by parley_set_side) (n := n) (by parley_set_side) (c := c) hH3 hH5).1 | (have h := (Parley.Proofs.Wiedijk.Ballot.LastPlace.last_place (m := m) (by parley_set_side) (n := n) (by parley_set_side) (c := c) hH3 hH5).1; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Wiedijk.Ballot.LastPlace.last_place (m := m) (by parley_set_side) (n := n) (by parley_set_side) (c := c) hH3 hH5).1; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | (parley_count_ext; exact_mod_cast (Parley.Proofs.Wiedijk.Ballot.LastPlace.last_place (m := m) (by parley_set_side) (n := n) (by parley_set_side) (c := c) hH3 hH5).1) | exact_mod_cast (Parley.Proofs.Wiedijk.Ballot.LastPlace.last_place (m := m) (by parley_set_side) (n := n) (by parley_set_side) (c := c) hH3 hH5).1 | exact_mod_cast ((Parley.Proofs.Wiedijk.Ballot.LastPlace.last_place (m := m) (by parley_set_side) (n := n) (by parley_set_side) (c := c) hH3 hH5).1).symm | (have h := (Parley.Proofs.Wiedijk.Ballot.LastPlace.last_place (m := m) (by parley_set_side) (n := n) (by parley_set_side) (c := c) hH3 hH5).1; rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Wiedijk.Ballot.LastPlace.last_place (m := m) (by parley_set_side) (n := n) (by parley_set_side) (c := c) hH3 hH5).1; qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Wiedijk.Ballot.LastPlace.last_place (m := m) (by parley_set_side) (n := n) (by parley_set_side) (c := c) hH3 hH5).1; parley_int_power h) | (have h := (Parley.Proofs.Wiedijk.Ballot.LastPlace.last_place (m := m) (by parley_set_side) (n := n) (by parley_set_side) (c := c) hH3 hH5).1; parley_set_side)
        have s2_2_1b : ((Set.Icc (1 : ℤ) (m + n) : Set ℤ) ∩ c).encard = ((m.toNat : ℕ) : ℕ∞) := by first | linear_combination (norm := parley_norm) (Parley.Proofs.Wiedijk.Ballot.LastPlace.last_place (m := m) (by parley_set_side) (n := n) (by parley_set_side) (c := c) hH3 hH5).2 | (have h := (Parley.Proofs.Wiedijk.Ballot.LastPlace.last_place (m := m) (by parley_set_side) (n := n) (by parley_set_side) (c := c) hH3 hH5).2; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Wiedijk.Ballot.LastPlace.last_place (m := m) (by parley_set_side) (n := n) (by parley_set_side) (c := c) hH3 hH5).2; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | (parley_count_ext; exact_mod_cast (Parley.Proofs.Wiedijk.Ballot.LastPlace.last_place (m := m) (by parley_set_side) (n := n) (by parley_set_side) (c := c) hH3 hH5).2) | exact_mod_cast (Parley.Proofs.Wiedijk.Ballot.LastPlace.last_place (m := m) (by parley_set_side) (n := n) (by parley_set_side) (c := c) hH3 hH5).2 | exact_mod_cast ((Parley.Proofs.Wiedijk.Ballot.LastPlace.last_place (m := m) (by parley_set_side) (n := n) (by parley_set_side) (c := c) hH3 hH5).2).symm | (have h := (Parley.Proofs.Wiedijk.Ballot.LastPlace.last_place (m := m) (by parley_set_side) (n := n) (by parley_set_side) (c := c) hH3 hH5).2; rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Wiedijk.Ballot.LastPlace.last_place (m := m) (by parley_set_side) (n := n) (by parley_set_side) (c := c) hH3 hH5).2; qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Wiedijk.Ballot.LastPlace.last_place (m := m) (by parley_set_side) (n := n) (by parley_set_side) (c := c) hH3 hH5).2; parley_int_power h) | (have h := (Parley.Proofs.Wiedijk.Ballot.LastPlace.last_place (m := m) (by parley_set_side) (n := n) (by parley_set_side) (c := c) hH3 hH5).2; parley_set_side)
        -- 2.2.2. calculation
        have s2_2_2 : ((Set.Icc (1 : ℤ) (m + n) : Set ℤ) \ c).encard < ((Set.Icc (1 : ℤ) (m + n) : Set ℤ) ∩ c).encard := by parley_count_after (by
          calc (((Set.Icc (1 : ℤ) (m + n) : Set ℤ) \ c).ncard : ℤ) = n := by first | parley_set_side | parley_line_toNat s2_2_1a | parley_line_toNat s2_2_1b
            _ < m := by parley_set_side
            _ = (((Set.Icc (1 : ℤ) (m + n) : Set ℤ) ∩ c).ncard : ℤ) := by first | parley_set_side | parley_line_toNat s2_2_1a | parley_line_toNat s2_2_1b)
        -- 2.2.3. substitute i = m + n (C1) into line 2.2.2
        have s2_2_3 : ((Set.Icc (1 : ℤ) i : Set ℤ) \ c).encard < ((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).encard := by parley_subst_at hC1 s2_2_2
        all_goals parley_set_side
      · skip
        -- 2.2.4. mun:range-bounds a := 1, b := m + n, k := i, from K1
        have s2_2_4a : 1 ≤ i := by first | linarith [(Parley.Items.Stdlib.Sums.mun_range_bounds_1 (a := (1 : ℤ)) (b := m + n) (k := i) hK1)] | (have h := (Parley.Items.Stdlib.Sums.mun_range_bounds_1 (a := (1 : ℤ)) (b := m + n) (k := i) hK1); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_range_bounds_1 (a := (1 : ℤ)) (b := m + n) (k := i) hK1) | (have h := (Parley.Items.Stdlib.Sums.mun_range_bounds_1 (a := (1 : ℤ)) (b := m + n) (k := i) hK1); parley_set_side)
        have s2_2_4b : i ≤ m + n := by first | linarith [(Parley.Items.Stdlib.Sums.mun_range_bounds_2 (a := (1 : ℤ)) (b := m + n) (k := i) hK1)] | (have h := (Parley.Items.Stdlib.Sums.mun_range_bounds_2 (a := (1 : ℤ)) (b := m + n) (k := i) hK1); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_range_bounds_2 (a := (1 : ℤ)) (b := m + n) (k := i) hK1) | (have h := (Parley.Items.Stdlib.Sums.mun_range_bounds_2 (a := (1 : ℤ)) (b := m + n) (k := i) hK1); parley_set_side)
        -- 2.2.5. inequalities, from C2, 2.2.4
        have s2_2_5 : i < m + n := by parley_order
        -- 2.2.6. mun:integer-step m := i, n := m + n, from 2.2.5
        have s2_2_6 : i + 1 ≤ m + n := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_integer_step (m := i) (n := m + n) s2_2_5)] | (have h := (Parley.Items.Stdlib.Numbers.mun_integer_step (m := i) (n := m + n) s2_2_5); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_integer_step (m := i) (n := m + n) s2_2_5) | (have h := (Parley.Items.Stdlib.Numbers.mun_integer_step (m := i) (n := m + n) s2_2_5); parley_set_side)
        -- 2.2.7. inequalities, from 2.2.6
        have s2_2_7 : i ≤ m + n - 1 := by parley_order
        -- 2.2.8. def:range-between k := i, a := 1, b := (m + n) − 1, from 2.2.4, 2.2.7
        have s2_2_8 : i ∈ Finset.Icc (1 : ℤ) (m + n - 1) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sums.def_range_between (k := i) (a := (1 : ℤ)) (b := m + n - 1))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sums.def_range_between (k := i) (a := (1 : ℤ)) (b := m + n - 1))).mpr (by parley_set_side); parley_set_side)
        -- 2.2.9. instantiate i := i in line 1, from 2.2.8
        have s2_2_9 : ((Set.Icc (1 : ℤ) i : Set ℤ) \ c).encard < ((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).encard := by first | linarith [(s1 i (by parley_set_side))] | (have h := (s1 i (by parley_set_side)); push_cast at h; linarith) | exact_mod_cast (s1 i (by parley_set_side)) | (have h := (s1 i (by parley_set_side)); parley_set_side)
        all_goals parley_set_side
    all_goals exact s2_2
  -- 3. D1, from 2
  have s3 : ∀ i : ℤ, i ∈ Finset.Icc 1 (m + n) → ((Set.Icc (1 : ℤ) i : Set ℤ) \ c).encard < ((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).encard := by parley_set_side
  all_goals exact s3

end Parley.Proofs.Wiedijk.Ballot.LeadToTheEnd
