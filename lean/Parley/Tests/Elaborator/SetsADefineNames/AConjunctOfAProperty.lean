module

public import SetTactics
public import Tactics
public import Batteries.Util.ExtendedBinder
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.SetNotationForOrder
public import Parley.Items.Stdlib.Sets

/-! Written from tests/elaborator/sets-a-define-names.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.SetsADefineNames.AConjunctOfAProperty

theorem a_conjunct_of_a_property (T : Set ℤ) (N : ℤ) (hH1 : 0 < N) (hH3 : T ∈ {S ∈ 𝒫 (Set.Icc (1 : ℤ) N : Set ℤ) | N ∈ S ∧ (∀ p ∈ S, p ≤ N)}) :
    (∀ p ∈ T, p ≤ N) := by
  -- 1. def:part-builder u := T, from H3
  have s1a : T ⊆ (Set.Icc (1 : ℤ) N : Set ℤ) := (((Parley.Items.Stdlib.Sets.def_part_builder (P := (fun S : Set ℤ => N ∈ S ∧ (∀ p ∈ S, p ≤ N))) (X := (Set.Icc (1 : ℤ) N : Set ℤ)) (u := T))).mp hH3).1
  have s1b : ∀ p ∈ T, p ≤ N := by first | exact (((Parley.Items.Stdlib.Sets.def_part_builder (P := (fun S : Set ℤ => N ∈ S ∧ (∀ p ∈ S, p ≤ N))) (X := (Set.Icc (1 : ℤ) N : Set ℤ)) (u := T))).mp hH3).2 | exact ((((Parley.Items.Stdlib.Sets.def_part_builder (P := (fun S : Set ℤ => N ∈ S ∧ (∀ p ∈ S, p ≤ N))) (X := (Set.Icc (1 : ℤ) N : Set ℤ)) (u := T))).mp hH3).2).symm | simpa using (((Parley.Items.Stdlib.Sets.def_part_builder (P := (fun S : Set ℤ => N ∈ S ∧ (∀ p ∈ S, p ≤ N))) (X := (Set.Icc (1 : ℤ) N : Set ℤ)) (u := T))).mp hH3).2 | exact_mod_cast (((Parley.Items.Stdlib.Sets.def_part_builder (P := (fun S : Set ℤ => N ∈ S ∧ (∀ p ∈ S, p ≤ N))) (X := (Set.Icc (1 : ℤ) N : Set ℤ)) (u := T))).mp hH3).2 | (have h := (((Parley.Items.Stdlib.Sets.def_part_builder (P := (fun S : Set ℤ => N ∈ S ∧ (∀ p ∈ S, p ≤ N))) (X := (Set.Icc (1 : ℤ) N : Set ℤ)) (u := T))).mp hH3).2; parley_set_side)
  -- 2. restate 1
  intro p h_p; parley_set_side

end Parley.Tests.Elaborator.SetsADefineNames.AConjunctOfAProperty
