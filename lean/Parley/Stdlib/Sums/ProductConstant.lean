module

public import AlgebraTactics
public import InstanceTactics
public import NormTactics
public import PowerTactics
public import SetTactics
public import Sets
public import SubstTactics
public import Tactics
public import Batteries.Util.ExtendedBinder
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Sets
public import Parley.Items.Stdlib.Sums

/-! Written from corpus/stdlib/sums.proof by parley build lean. -/

public section

namespace Parley.Stdlib.Sums.ProductConstant

set_option maxHeartbeats 400000 in
theorem product_constant {α : Type*} (X : Set α) (hH2 : X.Finite) (c : ℝ) :
    (∏ᶠ x ∈ X, (c : ℝ)) = c ^ X.ncard := by
  -- 1. induction on Y starting at ∅
  have r74_1 : X.Finite := by parley_set_side
  have s1 : ∀ Y ∈ 𝒫 X, (∏ᶠ x ∈ Y, (c : ℝ)) = c ^ Y.ncard := by
    refine LeanBridges.Sets.subset_induction hH2 ?_ ?_
    · skip
      -- 1.1. mun:product-empty
      have s1_1 : (∏ᶠ x ∈ (∅ : Set α), (c : ℝ)) = 1 := by exact (Parley.Items.Stdlib.Sums.mun_product_empty (X := Set.univ) (t := (fun x : α => c)))
      -- 1.2. algebra
      have s1_2 : c ^ 0 = 1 := by parley_ring
      -- 1.3. substitute
      have s1_3 : c ^ (∅ : Set α).ncard = 1 := by
        have c1 : 0 = ((∅ : Set α).ncard : ℤ) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.mun_card_empty (α := α)) | (have h := (Parley.Items.Stdlib.Counting.mun_card_empty (α := α)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_card_empty (α := α)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | (parley_count_ext; exact_mod_cast (Parley.Items.Stdlib.Counting.mun_card_empty (α := α))) | exact_mod_cast (Parley.Items.Stdlib.Counting.mun_card_empty (α := α)) | exact_mod_cast ((Parley.Items.Stdlib.Counting.mun_card_empty (α := α))).symm | (have h := (Parley.Items.Stdlib.Counting.mun_card_empty (α := α)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_card_empty (α := α)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_card_empty (α := α)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Counting.mun_card_empty (α := α)); parley_set_side)
        have c1_w : 0 = ((∅ : Set α).ncard : ℝ) := by have h := congrArg (fun x : ℤ => (x : ℝ)) c1; push_cast at h; linear_combination (norm := parley_norm) h
        have row1 : c ^ (∅ : Set α).ncard = 1 := by parley_count_int; first | parley_put_at c1_w s1_2 | parley_put_at c1 s1_2 | parley_subst_at c1_w s1_2 | parley_subst_at c1 s1_2
        exact row1
      -- 1.4. transitivity, from 1.1, 1.3
      parley_set_side
    · intro Y hK hIH
      intro a hK2
      -- 1.5. def:difference u := a, Y := X, Z := Y, from K2
      have s1_5 : a ∈ X ∧ ¬ a ∈ Y := by exact ((Parley.Items.Stdlib.Sets.def_difference (Y := X) (Z := Y) (u := a))).mp hK2
      -- 1.6. mun:finite-part, from H2, K
      have s1_6 : Y.Finite := by exact (Parley.Items.Stdlib.Counting.mun_finite_part (X := X) (Y := Y) hH2 hK)
      -- 1.7. mun:product-add-one, from K, 1.5, 1.6
      have s1_7 : (∏ᶠ x ∈ (Y ∪ ({a} : Set α)), (c : ℝ)) = (∏ᶠ x ∈ Y, (c : ℝ)) * c := by exact (Parley.Items.Stdlib.Sums.mun_product_add_one (t := (fun x : α => c)) (X := X) (Y := Y) (a := a) (by parley_set_side) s1_6 s1_5.1 s1_5.2)
      -- 1.8. mun:card-nat0 X := Y, from 1.6
      have s1_8 : 0 ≤ (Y.ncard : ℤ) := by exact (Parley.Items.Stdlib.Counting.mun_card_nat0 (X := Y) s1_6)
      -- 1.9. mun:exponent-step a := c, m := |Y|, from 1.8
      have s1_9 : c ^ (Y.ncard + 1) = c ^ Y.ncard * c := by
        have hI : c ^ (Y.ncard + 1) = c ^ Y.ncard * c := by parley_instance ((Parley.Items.Stdlib.Numbers.mun_exponent_step (a := c) (m := (Y.ncard : ℤ)) (by parley_set_side)))
        exact hI
      -- 1.10. substitute ∏(x ∈ Y) c = c^|Y| (IH) into line 1.7
      have s1_10 : (∏ᶠ x ∈ (Y ∪ ({a} : Set α)), (c : ℝ)) = c ^ Y.ncard * c := by (have h := Eq.subst (motive := (fun t : ℝ => (∏ᶠ x ∈ (Y ∪ ({a} : Set α)), (c : ℝ)) = t * c)) hIH s1_7; push_cast at h ⊢; all_goals exact_mod_cast h)
      -- 1.11. transitivity, from 1.10, 1.9
      have s1_11 : (∏ᶠ x ∈ (Y ∪ ({a} : Set α)), (c : ℝ)) = c ^ (Y.ncard + 1) := by parley_set_side
      -- 1.12. substitute
      have c1 : (Y.ncard : ℤ) + 1 = ((Y ∪ ({a} : Set α)).ncard : ℤ) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.mun_card_add_one (X := Y) (a := a) s1_6 s1_5.2) | (have h := (Parley.Items.Stdlib.Counting.mun_card_add_one (X := Y) (a := a) s1_6 s1_5.2); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_card_add_one (X := Y) (a := a) s1_6 s1_5.2); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | (parley_count_ext; exact_mod_cast (Parley.Items.Stdlib.Counting.mun_card_add_one (X := Y) (a := a) s1_6 s1_5.2)) | exact_mod_cast (Parley.Items.Stdlib.Counting.mun_card_add_one (X := Y) (a := a) s1_6 s1_5.2) | exact_mod_cast ((Parley.Items.Stdlib.Counting.mun_card_add_one (X := Y) (a := a) s1_6 s1_5.2)).symm | (have h := (Parley.Items.Stdlib.Counting.mun_card_add_one (X := Y) (a := a) s1_6 s1_5.2); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_card_add_one (X := Y) (a := a) s1_6 s1_5.2); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_card_add_one (X := Y) (a := a) s1_6 s1_5.2); parley_int_power h) | (have h := (Parley.Items.Stdlib.Counting.mun_card_add_one (X := Y) (a := a) s1_6 s1_5.2); parley_set_side)
      have c1_w : (Y.ncard : ℝ) + 1 = ((Y ∪ ({a} : Set α)).ncard : ℝ) := by have h := congrArg (fun x : ℤ => (x : ℝ)) c1; push_cast at h; linear_combination (norm := parley_norm) h
      have row1 : (∏ᶠ x ∈ (Y ∪ ({a} : Set α)), (c : ℝ)) = c ^ (Y ∪ ({a} : Set α)).ncard := by parley_count_int; first | parley_put_at c1_w s1_11 | parley_put_at c1 s1_11 | parley_subst_at c1_w s1_11 | parley_subst_at c1 s1_11
      exact row1
  -- 2. instantiate Y := X in line 1
  have r124_1 : X ⊆ X := by exact (Parley.Items.Stdlib.Sets.mun_subset_self (X := X))
  exact (s1 X (by parley_set_side))

end Parley.Stdlib.Sums.ProductConstant
