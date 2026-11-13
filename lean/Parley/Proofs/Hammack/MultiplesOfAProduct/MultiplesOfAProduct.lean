module

public import InstanceTactics
public import NormTactics
public import SetTactics
public import Tactics
public import Batteries.Util.ExtendedBinder
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.SetNotationForOrder
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/hammack/multiples-of-a-product.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.MultiplesOfAProduct.MultiplesOfAProduct

theorem multiples_of_a_product (m : ℤ) (n : ℤ) :
    {x : ℤ | m * n ∣ x} ⊆ {x : ℤ | m ∣ x} ∩ {x : ℤ | n ∣ x} := by
  -- 1. proof
  have s1 : ∀ t ∈ {x : ℤ | m * n ∣ x}, t ∈ {x : ℤ | m ∣ x} ∩ {x : ℤ | n ∣ x} := by
    intro t hK1
    -- 1.1. def:set-builder, from K1
    have s1_1 : m * n ∣ t := by
      have hI : m * n ∣ t := by parley_instance ((((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun x : ℤ => m * n ∣ x)) (X := (Set.univ : Set ℤ)) (u := t))).mp (by simpa only [Set.mem_ofPred_eq, Set.sep_univ] using hK1)).2)
      exact hI
    -- 1.2. obtain c: def:divides d := m·n, n := t, from 1.1
    obtain ⟨c, s1_2⟩ := ((Parley.Items.Stdlib.Divisibility.def_divides (d := m * n) (n := t))).mp s1_1
    -- 1.3. algebra, from 1.2
    have s1_3 : t = m * (n * c) := by linear_combination (norm := parley_norm) s1_2
    -- 1.4. def:divides d := m, n := t, from 1.1, 1.3
    have s1_4 : m ∣ t := ((Parley.Items.Stdlib.Divisibility.def_divides (d := m) (n := t))).mpr ⟨n * c, s1_3⟩
    -- 1.5. def:set-builder, from 1.1, 1.4
    have s1_5 : t ∈ {x : ℤ | m ∣ x} := by
      have hI : t ∈ {a : ℤ | m ∣ a} := by parley_instance (((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun x : ℤ => m ∣ x)) (X := (Set.univ : Set ℤ)) (u := t))).mpr ⟨Set.mem_univ _, s1_4⟩)
      exact hI
    -- 1.6. algebra, from 1.2
    have s1_6 : t = n * (m * c) := by linear_combination (norm := parley_norm) s1_2
    -- 1.7. def:divides d := n, n := t, from 1.1, 1.6
    have s1_7 : n ∣ t := ((Parley.Items.Stdlib.Divisibility.def_divides (d := n) (n := t))).mpr ⟨m * c, s1_6⟩
    -- 1.8. def:set-builder, from 1.1, 1.7
    have s1_8 : t ∈ {x : ℤ | n ∣ x} := by
      have hI : t ∈ {a : ℤ | n ∣ a} := by parley_instance (((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun x : ℤ => n ∣ x)) (X := (Set.univ : Set ℤ)) (u := t))).mpr ⟨Set.mem_univ _, s1_7⟩)
      exact hI
    -- 1.9. def:intersection u := t, from 1.5, 1.8
    exact ((Parley.Items.Stdlib.Sets.def_intersection (Y := {x : ℤ | m ∣ x}) (Z := {x : ℤ | n ∣ x}) (u := t))).mpr ⟨s1_5, s1_8⟩
  -- 2. def:subset, from 1
  exact ((Parley.Items.Stdlib.Sets.def_subset (X := {x : ℤ | m * n ∣ x}) (Y := {x : ℤ | m ∣ x} ∩ {x : ℤ | n ∣ x}))).mpr s1

end Parley.Proofs.Hammack.MultiplesOfAProduct.MultiplesOfAProduct
