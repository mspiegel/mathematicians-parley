module

public import NormTactics
public import PowerTactics
public import SetTactics
public import Sets
public import Tactics
public import Batteries.Util.ExtendedBinder
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Sets
public import Parley.Items.Stdlib.Sums

/-! Written from tests/elaborator/induction-over-a-set.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.InductionOverASet.AProductOfOnesByInduction

theorem a_product_of_ones_by_induction {α : Type*} (X : Set α) (hH2 : X.Finite) :
    (∏ᶠ x ∈ X, (1 : ℤ)) = 1 := by
  -- 1. induction on Y starting at ∅
  have r14_1 : X.Finite := by parley_set_side
  have s1 : ∀ Y ∈ 𝒫 X, (∏ᶠ y ∈ Y, (1 : ℤ)) = 1 := by
    refine LeanBridges.Sets.subset_induction (by parley_finite) ?_ ?_
    · skip
      -- 1.1. mun:product-empty
      exact (Parley.Items.Stdlib.Sums.mun_product_empty (X := Set.univ) (t := (fun y : α => (1 : ℤ))))
    · intro Y hK hIH
      intro a hK2
      -- 1.2. mun:finite-part, from H2, K
      have s1_2 : Y.Finite := by exact (Parley.Items.Stdlib.Counting.mun_finite_part (X := X) (Y := Y) hH2 hK)
      -- 1.3. def:difference u := a, Y := X, Z := Y, from K2
      have s1_3 : a ∈ X ∧ ¬ a ∈ Y := ((Parley.Items.Stdlib.Sets.def_difference (Y := X) (Z := Y) (u := a))).mp hK2
      -- 1.4. mun:product-add-one, from K, 1.2, 1.3
      have s1_4 : (∏ᶠ y ∈ (Y ∪ ({a} : Set α)), (1 : ℤ)) = (∏ᶠ y ∈ Y, (1 : ℤ)) * 1 := (Parley.Items.Stdlib.Sums.mun_product_add_one (t := (fun y : α => (1 : ℤ))) (X := X) (Y := Y) (a := a) (by parley_set_side) s1_2 s1_3.1 s1_3.2)
      -- 1.5. transitivity, from 1.4, IH
      parley_set_side
  -- 2. instantiate Y := X in line 1
  have r39_1 : X ⊆ X := by exact (Parley.Items.Stdlib.Sets.mun_subset_self (X := X))
  first | linear_combination (norm := parley_norm) (s1 X (by parley_set_side)) | (have h := (s1 X (by parley_set_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (s1 X (by parley_set_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (s1 X (by parley_set_side)) | exact_mod_cast ((s1 X (by parley_set_side))).symm | (have h := (s1 X (by parley_set_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (s1 X (by parley_set_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (s1 X (by parley_set_side)); parley_int_power h) | (have h := (s1 X (by parley_set_side)); parley_set_side)

end Parley.Tests.Elaborator.InductionOverASet.AProductOfOnesByInduction
