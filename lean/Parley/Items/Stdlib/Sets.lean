module

public import Sets
public import Tactics
public import Aesop.BuiltinRules
public import Batteries.Util.ExtendedBinder
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.BooleanAlgebra
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Insert
public import Mathlib.Data.Set.Lattice.Bounded
public import Mathlib.Data.Set.Lattice.Indexed
public import Mathlib.Data.Set.Operations
public import Mathlib.Order.Basic
public import Mathlib.Order.BooleanAlgebra.Set
public import Mathlib.Order.CompleteBooleanAlgebra
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.RelClasses
public import Mathlib.Order.SetNotation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Tactic.TypeStar

/-! Written from corpus/stdlib/sets.records by parley build lean. -/

public section

namespace Parley.Items.Stdlib.Sets

theorem axi_extensionality {α : Type*} (X : Set α) (Y : Set α) (h1 : ∀ t ∈ X, t ∈ Y) (h2 : ∀ t ∈ Y, t ∈ X) :
    X = Y :=
  by exact Set.Subset.antisymm h1 h2

theorem def_subset {α : Type*} (X : Set α) (Y : Set α) :
    X ⊆ Y ↔ (∀ t ∈ X, t ∈ Y) :=
  Iff.rfl

theorem def_set_builder {α : Type*} (P : α → Prop) (X : Set α) (u : α) :
    u ∈ {t ∈ X | P t} ↔ u ∈ X ∧ P u :=
  Set.mem_sep_iff

theorem def_part_builder {α : Type*} (P : Set α → Prop) (X : Set α) (u : Set α) :
    u ∈ {t ∈ 𝒫 X | P t} ↔ u ⊆ X ∧ P u :=
  by simp_all

theorem mun_part_builder_empty {α : Type*} (P : Set α → Prop) (X : Set α) :
    {t ∈ 𝒫 X | P t} = ∅ ↔ (∀ t ∈ 𝒫 X, ¬ P t) :=
  Set.sep_eq_empty_iff_mem_false

theorem mun_empty_subset {α : Type*} (X : Set α) :
    ∅ ⊆ X :=
  by simp_all

theorem mun_set_builder_subset {α : Type*} (P : α → Prop) (X : Set α) :
    {t ∈ X | P t} ⊆ X :=
  Set.sep_subset X P

theorem mun_set_builder_split {α : Type*} (P : α → Prop) (X : Set α) :
    X = {t ∈ X | P t} ∪ {t ∈ X | ¬ P t} :=
  by ext t; by_cases h : P t <;> simp [h]

theorem mun_set_builder_split_disjoint {α : Type*} (P : α → Prop) (X : Set α) :
    {t ∈ X | P t} ∩ {t ∈ X | ¬ P t} = ∅ :=
  by aesop

theorem mun_set_builder_empty {α : Type*} (P : α → Prop) (X : Set α) :
    {t ∈ X | P t} = ∅ ↔ (∀ t ∈ X, ¬ P t) :=
  by simp_all

theorem mun_subset_transitive {α : Type*} (X : Set α) (Y : Set α) (Z : Set α) (h1 : X ⊆ Y) (h2 : Y ⊆ Z) :
    X ⊆ Z :=
  h1.trans h2

theorem mun_subset_self {α : Type*} (X : Set α) :
    X ⊆ X :=
  Set.Subset.refl X

theorem def_powerset {α : Type*} (A : Set α) (S : Set α) :
    S ∈ 𝒫 A ↔ S ⊆ A :=
  Iff.rfl

theorem def_pair {α : Type*} (u : α) (w : α) (x : α) :
    x ∈ ({u, w} : Set α) ↔ x = u ∨ x = w :=
  Iff.rfl

theorem mun_pair_equal {α : Type*} (a : α) (b : α) (c : α) (d : α) :
    ({a, b} : Set α) = ({c, d} : Set α) ↔ a = c ∧ b = d ∨ a = d ∧ b = c :=
  Set.pair_eq_pair_iff

theorem def_singleton {α : Type*} (a : α) (x : α) :
    x ∈ ({a} : Set α) ↔ x = a :=
  Iff.rfl

theorem def_triple {α : Type*} (u : α) (v : α) (w : α) (x : α) :
    x ∈ ({u, v, w} : Set α) ↔ (x = u ∨ x = v) ∨ x = w :=
  by aesop

theorem mun_triple_members_1 {α : Type*} (u : α) (v : α) (w : α) :
    u ∈ ({u, v, w} : Set α) :=
  by simp

theorem mun_triple_members_2 {α : Type*} (u : α) (v : α) (w : α) :
    v ∈ ({u, v, w} : Set α) :=
  by simp

theorem mun_triple_members_3 {α : Type*} (u : α) (v : α) (w : α) :
    w ∈ ({u, v, w} : Set α) :=
  by simp

theorem mun_pair_finite {α : Type*} (u : α) (w : α) :
    ({u, w} : Set α).Finite :=
  by simp_all

theorem mun_subset_of_difference {α : Type*} (X : Set α) (Y : Set α) (a : α) (h1 : Y ⊆ X \ ({a} : Set α)) :
    ¬ a ∈ Y :=
  fun h => (h1 h).2 rfl

theorem mun_difference_of_union {α : Type*} (Y : Set α) (a : α) :
    (Y ∪ ({a} : Set α)) \ ({a} : Set α) = Y \ ({a} : Set α) :=
  by simp_all

theorem mun_difference_absent {α : Type*} (Y : Set α) (a : α) (h1 : ¬ a ∈ Y) :
    Y \ ({a} : Set α) = Y :=
  by simp_all

theorem mun_singleton_outside {α : Type*} (Y : Set α) (a : α) (h1 : ¬ a ∈ Y) :
    Y ∩ ({a} : Set α) = ∅ :=
  by simp_all

theorem mun_difference_by_union {α : Type*} (X : Set α) (Y : Set α) (Z : Set α) :
    X \ (Y ∪ Z) = (X \ Y) \ Z :=
  by aesop

theorem mun_nothing_left_outside {α : Type*} (X : Set α) (Y : Set α) :
    Y ⊆ X ↔ Y \ X = ∅ :=
  Iff.symm Set.sdiff_eq_empty

theorem mun_intersection_of_part {α : Type*} (X : Set α) (Y : Set α) (h1 : Y ⊆ X) :
    X ∩ Y = Y :=
  by simp_all

theorem mun_not_in_subset {α : Type*} (Y : Set α) (Z : Set α) (a : α) (h1 : ¬ a ∈ Z) (h2 : Y ⊆ Z) :
    ¬ a ∈ Y :=
  by tauto

theorem mun_in_union_singleton {α : Type*} (Y : Set α) (a : α) :
    a ∈ Y ∪ ({a} : Set α) :=
  by simp_all

theorem mun_listed_repeat {α : Type*} (a : α) (b : α) :
    ({a, b, b} : Set α) = ({a, b} : Set α) :=
  by (simp_all; done)

theorem mun_disjoint_empty {α : Type*} (Y : Set α) (Z : Set α) (h1 : ∀ s ∈ Z, ¬ s ∈ Y) :
    Y ∩ Z = ∅ :=
  LeanBridges.Sets.disjoint_empty Y Z h1

theorem mun_not_in_difference {α : Type*} (X : Set α) (a : α) :
    ¬ a ∈ X \ ({a} : Set α) :=
  by simp_all

theorem mun_union_subset {α : Type*} (X : Set α) (Y : Set α) (Z : Set α) (h1 : X ⊆ Z) (h2 : Y ⊆ Z) :
    X ∪ Y ⊆ Z :=
  Set.union_subset h1 h2

theorem mun_in_union_left {α : Type*} (Y : Set α) (Z : Set α) (u : α) (h1 : u ∈ Y) :
    u ∈ Y ∪ Z :=
  Or.inl h1

theorem mun_in_union_right {α : Type*} (Y : Set α) (Z : Set α) (u : α) (h1 : u ∈ Z) :
    u ∈ Y ∪ Z :=
  Or.inr h1

theorem mun_difference_subset {α : Type*} (X : Set α) (Y : Set α) :
    X \ Y ⊆ X :=
  Set.diff_subset

theorem mun_difference_shrinks {α : Type*} (X : Set α) (Y : Set α) (Z : Set α) (h1 : Y ⊆ X) :
    Y \ Z ⊆ X \ Z :=
  Set.diff_subset_diff_left h1

theorem mun_subset_into_difference {α : Type*} (X : Set α) (Y : Set α) (a : α) (h1 : Y ⊆ X) (h2 : ¬ a ∈ Y) :
    Y ⊆ X \ ({a} : Set α) :=
  Set.subset_sdiff_singleton h1 h2

theorem mun_remove_and_restore {α : Type*} (Y : Set α) (a : α) (h1 : a ∈ Y) :
    Y \ ({a} : Set α) ∪ ({a} : Set α) = Y :=
  by simp_all

theorem mun_singleton_subset {α : Type*} (X : Set α) (a : α) (h1 : a ∈ X) :
    ({a} : Set α) ⊆ X :=
  Set.singleton_subset_iff.mpr h1

theorem mun_pair_subset {α : Type*} (X : Set α) (a : α) (b : α) (h1 : a ∈ X) (h2 : b ∈ X) :
    ({a, b} : Set α) ⊆ X :=
  LeanBridges.Sets.pair_subset X a b h1 h2

theorem mun_triple_subset {α : Type*} (X : Set α) (a : α) (b : α) (c : α) (h1 : a ∈ X) (h2 : b ∈ X) (h3 : c ∈ X) :
    ({a, b, c} : Set α) ⊆ X :=
  by intro x hx; rcases hx with rfl | rfl | rfl <;> assumption

theorem mun_powerset_monotone {α : Type*} (X : Set α) (Y : Set α) (h1 : Y ⊆ X) :
    𝒫 Y ⊆ 𝒫 X :=
  Set.powerset_mono.mpr h1

theorem def_intersection {α : Type*} (Y : Set α) (Z : Set α) (u : α) :
    u ∈ Y ∩ Z ↔ u ∈ Y ∧ u ∈ Z :=
  Iff.rfl

theorem def_union {α : Type*} (Y : Set α) (Z : Set α) (u : α) :
    u ∈ Y ∪ Z ↔ u ∈ Y ∨ u ∈ Z :=
  Iff.rfl

theorem mun_remove_member {α : Type*} (Y : Set α) (a : α) (u : α) :
    u ∈ Y \ ({a} : Set α) ↔ u ∈ Y ∧ ¬ u = a :=
  Set.mem_diff_singleton

theorem mun_intersection_commutes {α : Type*} (Y : Set α) (Z : Set α) :
    Y ∩ Z = Z ∩ Y :=
  Set.inter_comm Y Z

theorem mun_union_commutes {α : Type*} (Y : Set α) (Z : Set α) :
    Y ∪ Z = Z ∪ Y :=
  Set.union_comm Y Z

theorem mun_union_difference {α : Type*} (Y : Set α) (Z : Set α) :
    Y ∪ Z \ Y = Y ∪ Z :=
  Set.union_diff_self

theorem mun_nonempty_member {α : Type*} (Y : Set α) (h1 : ¬ Y = ∅) :
    ∃ a ∈ Y, True :=
  by obtain ⟨a, ha⟩ := Set.nonempty_iff_ne_empty.2 h1; exact ⟨a, ha, trivial⟩

theorem mun_member_nonempty {α : Type*} (Y : Set α) (a : α) (h1 : a ∈ Y) :
    ¬ Y = ∅ :=
  by aesop

theorem mun_intersection_self {α : Type*} (Y : Set α) :
    Y ∩ Y = Y :=
  Set.inter_self Y

theorem mun_union_self {α : Type*} (Y : Set α) :
    Y ∪ Y = Y :=
  Set.union_self Y

theorem mun_union_empty {α : Type*} (Y : Set α) :
    Y ∪ ∅ = Y :=
  Set.union_empty Y

theorem mun_intersection_empty {α : Type*} (Y : Set α) :
    Y ∩ ∅ = ∅ :=
  by (simp_all; done)

theorem mun_difference_self {α : Type*} (Y : Set α) :
    Y \ Y = ∅ :=
  Set.sdiff_self

theorem mun_difference_empty {α : Type*} (Y : Set α) :
    Y \ ∅ = Y :=
  by (simp_all; done)

theorem mun_intersection_distributes {α : Type*} (X : Set α) (Y : Set α) (Z : Set α) :
    X ∩ (Y ∪ Z) = X ∩ Y ∪ X ∩ Z :=
  by aesop

theorem mun_intersection_distributes_right {α : Type*} (X : Set α) (Y : Set α) (Z : Set α) :
    (X ∪ Y) ∩ Z = X ∩ Z ∪ Y ∩ Z :=
  by aesop

theorem mun_intersection_distributes_over_intersection {α : Type*} (X : Set α) (Y : Set α) (Z : Set α) :
    (X ∩ Y) ∩ Z = (X ∩ Z) ∩ (Y ∩ Z) :=
  by aesop

theorem mun_intersection_subset {α : Type*} (Y : Set α) (Z : Set α) :
    Y ∩ Z ⊆ Y :=
  by simp_all

theorem mun_intersection_and_difference {α : Type*} (Y : Set α) (Z : Set α) :
    Y ∩ Z ∪ Y \ Z = Y :=
  by simp_all

theorem mun_intersection_and_difference_disjoint {α : Type*} (Y : Set α) (Z : Set α) :
    (Y ∩ Z) ∩ (Y \ Z) = ∅ :=
  by aesop

theorem mun_subset_empty {α : Type*} (Y : Set α) :
    Y ⊆ ∅ ↔ Y = ∅ :=
  Set.subset_empty_iff

theorem def_difference {α : Type*} (Y : Set α) (Z : Set α) (u : α) :
    u ∈ Y \ Z ↔ u ∈ Y ∧ ¬ u ∈ Z :=
  Iff.rfl

theorem mun_in_subset {α : Type*} (X : Set α) (Y : Set α) (u : α) (h1 : X ⊆ Y) (h2 : u ∈ X) :
    u ∈ Y :=
  h1 h2

theorem mun_difference_reverses {α : Type*} (X : Set α) (Y : Set α) (Z : Set α) (h1 : X ⊆ Y) :
    Z \ Y ⊆ Z \ X :=
  Set.sdiff_subset_sdiff (fun ⦃a⦄ a_1 => a_1) h1

theorem mun_complement_swap {α : Type*} (X : Set α) (Y : Set α) (Z : Set α) (h1 : X ⊆ Z) (h2 : Y ⊆ Z) :
    X ⊆ Z \ Y ↔ Y ⊆ Z \ X :=
  ⟨fun h x hx => ⟨h2 hx, fun hX => (h hX).2 hx⟩, fun h x hx => ⟨h1 hx, fun hY => (h hY).2 hx⟩⟩

theorem mun_complement_swap_outside {α : Type*} (X : Set α) (Y : Set α) (Z : Set α) :
    Z \ Y ⊆ X ↔ Z \ X ⊆ Y :=
  Set.sdiff_subset_comm

theorem mun_equal_subset {α : Type*} (X : Set α) (Y : Set α) (h1 : X = Y) :
    X ⊆ Y :=
  by simp_all

theorem mun_disjoint_within {α : Type*} (X : Set α) (Y : Set α) (Z : Set α) (h1 : X ⊆ Y) (h2 : Y ∩ Z = ∅) :
    X ∩ Z = ∅ :=
  Set.eq_empty_of_subset_empty (h2 ▸ Set.inter_subset_inter_left Z h1)

theorem mun_disjoint_member {α : Type*} (Y : Set α) (Z : Set α) (u : α) (h1 : Y ∩ Z = ∅) (h2 : u ∈ Y) :
    ¬ u ∈ Z :=
  LeanBridges.Sets.disjoint_member Y Z u h1 h2

theorem mun_disjoint_difference {α : Type*} (Y : Set α) (Z : Set α) :
    Y ∩ (Z \ Y) = ∅ :=
  by simp_all

theorem def_indexed_union {α : Type*} (D : Set (Set α)) (u : α) :
    u ∈ (⋃ X ∈ D, X) ↔ (∃ X ∈ D, u ∈ X) :=
  by (simp_all; done)

theorem mun_union_contains_member {α : Type*} (D : Set (Set α)) (Y : Set α) (h1 : Y ∈ D) :
    Y ⊆ (⋃ X ∈ D, X) :=
  Set.subset_biUnion_of_mem (u := fun X => X) h1

theorem mun_union_within {α : Type*} (D : Set (Set α)) (Z : Set α) (h1 : ∀ X ∈ D, X ⊆ Z) :
    (⋃ X ∈ D, X) ⊆ Z :=
  by (simp_all; done)

theorem mun_subset_antisymmetric {α : Type*} (X : Set α) (Y : Set α) (h1 : X ⊆ Y) (h2 : Y ⊆ X) :
    X = Y :=
  Set.Subset.antisymm h1 h2

end Parley.Items.Stdlib.Sets
