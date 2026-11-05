module

public import OrderTactics
public import PowerTactics
public import SetTactics
public import SubstTactics
public import Tactics
public import Parley.Items.Proofs.Wiedijk.Ballot
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Reasoning
public import Parley.Items.Stdlib.Sums
public import Parley.Proofs.Wiedijk.Ballot.LastPlace

/-! Written from proofs/wiedijk/ballot.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.Ballot.LeadToTheEnd

set_option maxHeartbeats 400000 in
theorem lead_to_the_end (m : ℕ) (n : ℕ) (c : Set ℤ) (hH3 : c ⊆ (Set.Icc (1 : ℤ) ((m : ℤ) + (n : ℤ)) : Set ℤ)) (hH4 : (n : ℤ) < (m : ℤ)) (hH5 : c.encard = ((m : ℕ) : ℕ∞)) (hH6 : ∀ i : ℤ, i ∈ Finset.Icc 1 ((m : ℤ) + (n : ℤ) - 1) → ((Set.Icc (1 : ℤ) i : Set ℤ) \ c).encard < ((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).encard) :
    (∀ i : ℤ, i ∈ Finset.Icc 1 ((m : ℤ) + (n : ℤ)) → ((Set.Icc (1 : ℤ) i : Set ℤ) \ c).encard < ((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).encard) := by
  -- 1. D1, from H6
  have s1 : ∀ i : ℤ, i ∈ Finset.Icc 1 ((m : ℤ) + (n : ℤ) - 1) → ((Set.Icc (1 : ℤ) i : Set ℤ) \ c).encard < ((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).encard := by parley_set_side
  -- 2. proof
  have s2 : ∀ i : ℤ, i ∈ Finset.Icc 1 ((m : ℤ) + (n : ℤ)) → ((Set.Icc (1 : ℤ) i : Set ℤ) \ c).encard < ((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).encard := by
    intro i hK1
    try push_cast at hK1
    try have hK1_bounds := Finset.mem_Icc.mp hK1
    -- 2.1. axi:excluded-middle P := i = m + n
    have s2_1 : i = (m : ℤ) + (n : ℤ) ∨ i ≠ (m : ℤ) + (n : ℤ) := by first | exact (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := i = (m : ℤ) + (n : ℤ))) | exact ((Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := i = (m : ℤ) + (n : ℤ)))).symm | simpa using (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := i = (m : ℤ) + (n : ℤ))) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := i = (m : ℤ) + (n : ℤ))) | (have h := (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := i = (m : ℤ) + (n : ℤ))); parley_set_side)
    -- 2.2. cases, from 2.1
    have s2_2 : ((Set.Icc (1 : ℤ) i : Set ℤ) \ c).encard < ((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).encard := by
      rcases s2_1 with hC1 | hC2
      · skip
        -- 2.2.1. thm:last-place, from H3, H5
        have s2_2_1a : ((Set.Icc (1 : ℤ) ((m : ℤ) + (n : ℤ)) : Set ℤ) \ c).encard = ((n : ℕ) : ℕ∞) := by first | linear_combination (norm := parley_norm) (Parley.Proofs.Wiedijk.Ballot.LastPlace.last_place (m := m) (n := n) (c := c) (by parley_set_side) (by parley_set_side)).1 | (have h := (Parley.Proofs.Wiedijk.Ballot.LastPlace.last_place (m := m) (n := n) (c := c) (by parley_set_side) (by parley_set_side)).1; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Wiedijk.Ballot.LastPlace.last_place (m := m) (n := n) (c := c) (by parley_set_side) (by parley_set_side)).1; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | (parley_count_ext; exact_mod_cast (Parley.Proofs.Wiedijk.Ballot.LastPlace.last_place (m := m) (n := n) (c := c) (by parley_set_side) (by parley_set_side)).1) | exact_mod_cast (Parley.Proofs.Wiedijk.Ballot.LastPlace.last_place (m := m) (n := n) (c := c) (by parley_set_side) (by parley_set_side)).1 | exact_mod_cast ((Parley.Proofs.Wiedijk.Ballot.LastPlace.last_place (m := m) (n := n) (c := c) (by parley_set_side) (by parley_set_side)).1).symm | (have h := (Parley.Proofs.Wiedijk.Ballot.LastPlace.last_place (m := m) (n := n) (c := c) (by parley_set_side) (by parley_set_side)).1; rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Wiedijk.Ballot.LastPlace.last_place (m := m) (n := n) (c := c) (by parley_set_side) (by parley_set_side)).1; qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Wiedijk.Ballot.LastPlace.last_place (m := m) (n := n) (c := c) (by parley_set_side) (by parley_set_side)).1; parley_int_power h) | (have h := (Parley.Proofs.Wiedijk.Ballot.LastPlace.last_place (m := m) (n := n) (c := c) (by parley_set_side) (by parley_set_side)).1; parley_set_side)
        have s2_2_1b : ((Set.Icc (1 : ℤ) ((m : ℤ) + (n : ℤ)) : Set ℤ) ∩ c).encard = ((m : ℕ) : ℕ∞) := by first | linear_combination (norm := parley_norm) (Parley.Proofs.Wiedijk.Ballot.LastPlace.last_place (m := m) (n := n) (c := c) (by parley_set_side) (by parley_set_side)).2 | (have h := (Parley.Proofs.Wiedijk.Ballot.LastPlace.last_place (m := m) (n := n) (c := c) (by parley_set_side) (by parley_set_side)).2; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Wiedijk.Ballot.LastPlace.last_place (m := m) (n := n) (c := c) (by parley_set_side) (by parley_set_side)).2; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | (parley_count_ext; exact_mod_cast (Parley.Proofs.Wiedijk.Ballot.LastPlace.last_place (m := m) (n := n) (c := c) (by parley_set_side) (by parley_set_side)).2) | exact_mod_cast (Parley.Proofs.Wiedijk.Ballot.LastPlace.last_place (m := m) (n := n) (c := c) (by parley_set_side) (by parley_set_side)).2 | exact_mod_cast ((Parley.Proofs.Wiedijk.Ballot.LastPlace.last_place (m := m) (n := n) (c := c) (by parley_set_side) (by parley_set_side)).2).symm | (have h := (Parley.Proofs.Wiedijk.Ballot.LastPlace.last_place (m := m) (n := n) (c := c) (by parley_set_side) (by parley_set_side)).2; rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Wiedijk.Ballot.LastPlace.last_place (m := m) (n := n) (c := c) (by parley_set_side) (by parley_set_side)).2; qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Wiedijk.Ballot.LastPlace.last_place (m := m) (n := n) (c := c) (by parley_set_side) (by parley_set_side)).2; parley_int_power h) | (have h := (Parley.Proofs.Wiedijk.Ballot.LastPlace.last_place (m := m) (n := n) (c := c) (by parley_set_side) (by parley_set_side)).2; parley_set_side)
        -- 2.2.2. calculation
        have s2_2_2 : ((Set.Icc (1 : ℤ) ((m : ℤ) + (n : ℤ)) : Set ℤ) \ c).encard < ((Set.Icc (1 : ℤ) ((m : ℤ) + (n : ℤ)) : Set ℤ) ∩ c).encard := by parley_count_after (by
          calc (((Set.Icc (1 : ℤ) ((m : ℤ) + (n : ℤ)) : Set ℤ) \ c).ncard : ℤ) = (n : ℤ) := by parley_set_side
            _ < (m : ℤ) := by parley_set_side
            _ = (((Set.Icc (1 : ℤ) ((m : ℤ) + (n : ℤ)) : Set ℤ) ∩ c).ncard : ℤ) := by parley_set_side)
        -- 2.2.3. substitute i = m + n (C1) into line 2.2.2
        have s2_2_3 : ((Set.Icc (1 : ℤ) i : Set ℤ) \ c).encard < ((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).encard := by parley_subst_at hC1 s2_2_2
        all_goals parley_set_side
      · skip
        -- 2.2.4. mun:range-bounds a := 1, b := m + n, k := i, from K1
        have s2_2_4a : 1 ≤ i := by first | linarith [(Parley.Items.Stdlib.Sums.mun_range_bounds_1 (a := (1 : ℤ)) (b := (m : ℤ) + (n : ℤ)) (k := i) hK1)] | (have h := (Parley.Items.Stdlib.Sums.mun_range_bounds_1 (a := (1 : ℤ)) (b := (m : ℤ) + (n : ℤ)) (k := i) hK1); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_range_bounds_1 (a := (1 : ℤ)) (b := (m : ℤ) + (n : ℤ)) (k := i) hK1) | (have h := (Parley.Items.Stdlib.Sums.mun_range_bounds_1 (a := (1 : ℤ)) (b := (m : ℤ) + (n : ℤ)) (k := i) hK1); parley_set_side)
        have s2_2_4b : i ≤ (m : ℤ) + (n : ℤ) := by first | linarith [(Parley.Items.Stdlib.Sums.mun_range_bounds_2 (a := (1 : ℤ)) (b := (m : ℤ) + (n : ℤ)) (k := i) hK1)] | (have h := (Parley.Items.Stdlib.Sums.mun_range_bounds_2 (a := (1 : ℤ)) (b := (m : ℤ) + (n : ℤ)) (k := i) hK1); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_range_bounds_2 (a := (1 : ℤ)) (b := (m : ℤ) + (n : ℤ)) (k := i) hK1) | (have h := (Parley.Items.Stdlib.Sums.mun_range_bounds_2 (a := (1 : ℤ)) (b := (m : ℤ) + (n : ℤ)) (k := i) hK1); parley_set_side)
        -- 2.2.5. inequalities, from C2, 2.2.4
        have s2_2_5 : i < (m : ℤ) + (n : ℤ) := by parley_order
        -- 2.2.6. mun:integer-step m := i, n := m + n, from 2.2.5
        have s2_2_6 : i + 1 ≤ (m : ℤ) + (n : ℤ) := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_integer_step (m := i) (n := (m : ℤ) + (n : ℤ)) s2_2_5)] | (have h := (Parley.Items.Stdlib.Numbers.mun_integer_step (m := i) (n := (m : ℤ) + (n : ℤ)) s2_2_5); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_integer_step (m := i) (n := (m : ℤ) + (n : ℤ)) s2_2_5) | (have h := (Parley.Items.Stdlib.Numbers.mun_integer_step (m := i) (n := (m : ℤ) + (n : ℤ)) s2_2_5); parley_set_side)
        -- 2.2.7. inequalities, from 2.2.6
        have s2_2_7 : i ≤ (m : ℤ) + (n : ℤ) - 1 := by parley_order
        -- 2.2.8. def:range-between k := i, a := 1, b := (m + n) − 1, from 2.2.4, 2.2.7
        have s2_2_8 : i ∈ Finset.Icc (1 : ℤ) ((m : ℤ) + (n : ℤ) - 1) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sums.def_range_between (k := i) (a := (1 : ℤ)) (b := (m : ℤ) + (n : ℤ) - 1))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sums.def_range_between (k := i) (a := (1 : ℤ)) (b := (m : ℤ) + (n : ℤ) - 1))).mpr (by parley_set_side); parley_set_side)
        -- 2.2.9. instantiate i := i in line 1, from 2.2.8
        have s2_2_9 : ((Set.Icc (1 : ℤ) i : Set ℤ) \ c).encard < ((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).encard := by first | linarith [(s1 i (by parley_set_side))] | (have h := (s1 i (by parley_set_side)); push_cast at h; linarith) | exact_mod_cast (s1 i (by parley_set_side)) | (have h := (s1 i (by parley_set_side)); parley_set_side)
        all_goals parley_set_side
    all_goals exact s2_2
  -- 3. D1, from 2
  have s3 : ∀ i : ℤ, i ∈ Finset.Icc 1 ((m : ℤ) + (n : ℤ)) → ((Set.Icc (1 : ℤ) i : Set ℤ) \ c).encard < ((Set.Icc (1 : ℤ) i : Set ℤ) ∩ c).encard := by parley_set_side
  all_goals exact s3

end Parley.Proofs.Wiedijk.Ballot.LeadToTheEnd
