module

public import NormTactics
public import PowerTactics
public import SetTactics
public import SubstTactics
public import Tactics
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Data.ENat.Defs
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Reasoning
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/setmm/two-elements.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.TwoElements.TwoElements

set_option maxHeartbeats 600000 in
theorem two_elements {α : Type*} (V : Set α) :
    (V.encard = ((2 : ℕ) : ℕ∞) ↔ (∃ a ∈ V, ∃ b ∈ V, ¬ a = b ∧ V = ({a, b} : Set α))) := by
  -- the theorem. both directions
  constructor
  · skip
    intro hC1
    -- 1. calculation
    have s1 : V.encard = ((1 + 1 : ℕ) : ℕ∞) := by parley_count_after (by
      calc V.encard = ((2 : ℕ) : ℕ∞) := by parley_set_side
        _ = ((1 + 1 : ℕ) : ℕ∞) := by norm_num)
    -- 2. obtain b: mun:card-nonempty X := V, k := 1, from 1
    obtain ⟨b, s2, _⟩ := (Parley.Items.Stdlib.Counting.mun_card_nonempty (X := V) (k := (1 : ℤ)) (by parley_set_side) (by parley_set_side))
    -- 3. mun:card-remove X := V, a := b, k := 1, from 1, 2
    have s3 : (V \ ({b} : Set α)).encard = ((1 : ℕ) : ℕ∞) := by (have h := (Parley.Items.Stdlib.Counting.mun_card_remove (X := V) (a := b) s2 (k := (1 : ℤ)) (by parley_set_side) (by parley_set_side)); simp only [← Set.Finite.cast_ncard_eq (show (V \ {b} : Set α).Finite by parley_finite)] at h ⊢; exact_mod_cast h)
    -- 4. obtain a: mun:card-nonempty X := V ∖ {b}, k := 0, from 3
    obtain ⟨a, s4, _⟩ := (Parley.Items.Stdlib.Counting.mun_card_nonempty (X := V \ ({b} : Set α)) (k := (0 : ℤ)) (by parley_set_side) (by parley_set_side))
    -- 5. mun:remove-member u := a, Y := V, a := b, from 4
    have s5a : a ∈ V := (((Parley.Items.Stdlib.Sets.mun_remove_member (Y := V) (a := b) (u := a))).mp s4).1
    have s5b : ¬ a = b := (((Parley.Items.Stdlib.Sets.mun_remove_member (Y := V) (a := b) (u := a))).mp s4).2
    -- 6. mun:card-remove X := V ∖ {b}, k := 0, from 3, 4
    have s6 : ((V \ ({b} : Set α)) \ ({a} : Set α)).encard = ((0 : ℕ) : ℕ∞) := by (have h := (Parley.Items.Stdlib.Counting.mun_card_remove (X := V \ ({b} : Set α)) (a := a) s4 (k := (0 : ℤ)) (by parley_set_side) (by parley_set_side)); simp only [← Set.Finite.cast_ncard_eq (show ((V \ {b}) \ {a} : Set α).Finite by parley_finite)] at h ⊢; exact_mod_cast h)
    -- 7. proof
    have s7 : ∀ t ∈ V, t ∈ ({a, b} : Set α) := by
      intro t hK1
      -- 7.1. axi:excluded-middle P := t = b
      have s7_1 : t = b ∨ ¬ t = b := by exact (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := t = b))
      -- 7.2. cases, from 7.1
      rcases s7_1 with hC2 | hC3
      · skip
        -- 7.2.1. mun:or-right P := t = a, Q := t = b, from C2
        have s7_2_1 : t = a ∨ t = b := by exact (Parley.Items.Stdlib.Reasoning.mun_or_right (P := t = a) (Q := t = b) hC2)
        -- 7.2.2. def:pair x := t, u := a, w := b, from 7.2.1
        first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_pair (u := a) (w := b) (x := t))).mpr s7_2_1 | (have h := ((Parley.Items.Stdlib.Sets.def_pair (u := a) (w := b) (x := t))).mpr s7_2_1; parley_set_side)
      · skip
        -- 7.2.3. mun:remove-member u := t, Y := V, a := b, from C3, K1
        have s7_2_3 : t ∈ V \ ({b} : Set α) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.mun_remove_member (Y := V) (a := b) (u := t))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.mun_remove_member (Y := V) (a := b) (u := t))).mpr (by parley_set_side); parley_set_side)
        -- 7.2.4. axi:excluded-middle P := t = a
        have s7_2_4 : t = a ∨ ¬ t = a := by exact (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := t = a))
        -- 7.2.5. cases, from 7.2.4
        rcases s7_2_4 with hC4 | hC5
        · skip
          -- 7.2.5.1. mun:or-left P := t = a, Q := t = b, from C4
          have s7_2_5_1 : t = a ∨ t = b := by exact (Parley.Items.Stdlib.Reasoning.mun_or_left (P := t = a) (Q := t = b) hC4)
          -- 7.2.5.2. def:pair x := t, u := a, w := b, from 7.2.5.1
          first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_pair (u := a) (w := b) (x := t))).mpr s7_2_5_1 | (have h := ((Parley.Items.Stdlib.Sets.def_pair (u := a) (w := b) (x := t))).mpr s7_2_5_1; parley_set_side)
        · skip
          -- 7.2.5.3. mun:remove-member u := t, Y := V ∖ {b}, from C5, 7.2.3
          have s7_2_5_3 : t ∈ (V \ ({b} : Set α)) \ ({a} : Set α) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.mun_remove_member (Y := V \ ({b} : Set α)) (a := a) (u := t))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.mun_remove_member (Y := V \ ({b} : Set α)) (a := a) (u := t))).mpr (by parley_set_side); parley_set_side)
          -- 7.2.5.4. substitute
          have s7_2_5_4 : t ∈ (∅ : Set α) := by parley_count_after (by
            have c1 : (V \ ({b} : Set α)) \ ({a} : Set α) = ∅ := by exact (Parley.Items.Stdlib.Counting.mun_card_zero (X := (V \ ({b} : Set α)) \ ({a} : Set α)) (by parley_set_side))
            have row1 : t ∈ (∅ : Set α) := by parley_subst_at c1 s7_2_5_3
            exact row1)
          -- 7.2.5.5. inspection
          have s7_2_5_5 : ¬ t ∈ (∅ : Set α) := by parley_set_side
          exact absurd s7_2_5_4 s7_2_5_5
    -- 8. def:subset X := V, Y := {a, b}, from 7
    have s8 : V ⊆ ({a, b} : Set α) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_subset (X := V) (Y := ({a, b} : Set α)))).mpr s7 | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := V) (Y := ({a, b} : Set α)))).mpr s7; parley_set_side)
    -- 9. mun:pair-subset X := V, from 2, 5
    have s9 : ({a, b} : Set α) ⊆ V := by exact (Parley.Items.Stdlib.Sets.mun_pair_subset (X := V) (a := a) (b := b) s5a s2)
    -- 10. mun:subset-antisymmetric X := V, Y := {a, b}, from 8, 9
    have s10 : V = ({a, b} : Set α) := by exact (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := V) (Y := ({a, b} : Set α)) s8 s9)
    -- 11. exhibit, from 2, 5, 10
    exact ⟨b, by parley_set_side, a, by parley_set_side, ⟨by parley_set_side, by parley_set_side⟩⟩
  · skip
    intro hC6
    -- 12. obtain c, d from C6
    obtain ⟨c, s12a, d, s12b, ⟨s12c, s12d⟩⟩ := hC6
    -- 13. calculation
    parley_count_after (by
      calc V.encard = ((({c, d} : Set α).ncard : ℕ) : ℕ∞) := by parley_subst s12d
        _ = ((2 : ℕ) : ℕ∞) := by first | linear_combination (norm := parley_norm) ((Parley.Items.Stdlib.Counting.mun_card_pair_distinct (u := c) (w := d))).mp s12c | (have h := ((Parley.Items.Stdlib.Counting.mun_card_pair_distinct (u := c) (w := d))).mp s12c; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := ((Parley.Items.Stdlib.Counting.mun_card_pair_distinct (u := c) (w := d))).mp s12c; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | (parley_count_ext; exact_mod_cast ((Parley.Items.Stdlib.Counting.mun_card_pair_distinct (u := c) (w := d))).mp s12c) | exact_mod_cast ((Parley.Items.Stdlib.Counting.mun_card_pair_distinct (u := c) (w := d))).mp s12c | exact_mod_cast (((Parley.Items.Stdlib.Counting.mun_card_pair_distinct (u := c) (w := d))).mp s12c).symm | (have h := ((Parley.Items.Stdlib.Counting.mun_card_pair_distinct (u := c) (w := d))).mp s12c; rify; linear_combination (norm := parley_norm) h) | (have h := ((Parley.Items.Stdlib.Counting.mun_card_pair_distinct (u := c) (w := d))).mp s12c; qify; linear_combination (norm := parley_norm) h) | (have h := ((Parley.Items.Stdlib.Counting.mun_card_pair_distinct (u := c) (w := d))).mp s12c; parley_int_power h) | (have h := ((Parley.Items.Stdlib.Counting.mun_card_pair_distinct (u := c) (w := d))).mp s12c; parley_set_side))

end Parley.Proofs.Setmm.TwoElements.TwoElements
