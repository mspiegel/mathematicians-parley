module

public import Graphs
public import Batteries.Util.ExtendedBinder
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.ENat.Defs
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Data.Sym.Sym2
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.TypeStar

/-! Written from corpus/stdlib/graphs.records by parley build lean. -/

public section

namespace Parley.Items.Stdlib.Graphs

theorem def_traversable {α β : Type*} [Nonempty α] [Nonempty β] (E : Set β) (V : Set α) (G : β → Sym2 α) [LeanBridges.Graphs.Multigraph V E G] :
    (∃ n : ℤ, 0 ≤ n ∧ (∃ e : ℤ → β, Set.MapsTo e (Set.Icc (1 : ℤ) n : Set ℤ) E ∧ (∃ v : ℤ → α, Set.MapsTo v (Set.Icc (0 : ℤ) n : Set ℤ) V ∧ (((∀ i : ℤ, i ∈ Finset.Icc 1 n → G (e i) = Sym2.mk (v (i - 1)) (v i)) ∧ Set.MapsTo e (Set.Icc (1 : ℤ) n : Set ℤ) E ∧ Set.InjOn e (Set.Icc (1 : ℤ) n : Set ℤ)) ∧ (∀ a ∈ E, ∃ i : ℤ, i ∈ Finset.Icc 1 n ∧ a = e i))))) ↔ (∃ n : ℤ, 0 ≤ n ∧ (∃ e : ℤ → β, Set.MapsTo e (Set.Icc (1 : ℤ) n : Set ℤ) E ∧ (∃ v : ℤ → α, Set.MapsTo v (Set.Icc (0 : ℤ) n : Set ℤ) V ∧ (((∀ i : ℤ, i ∈ Finset.Icc 1 n → G (e i) = Sym2.mk (v (i - 1)) (v i)) ∧ Set.MapsTo e (Set.Icc (1 : ℤ) n : Set ℤ) E ∧ Set.InjOn e (Set.Icc (1 : ℤ) n : Set ℤ)) ∧ (∀ a ∈ E, ∃ i : ℤ, i ∈ Finset.Icc 1 n ∧ a = e i))))) :=
  Iff.rfl

theorem def_walk {α β : Type*} [Nonempty α] [Nonempty β] (V : Set α) (E : Set β) (G : β → Sym2 α) [LeanBridges.Graphs.Multigraph V E G] (e : ℤ → β) (v : ℤ → α) (n : ℤ) (h1 : 0 ≤ n) (he : Set.MapsTo e (Set.Icc (1 : ℤ) n : Set ℤ) E) (hv : Set.MapsTo v (Set.Icc (0 : ℤ) n : Set ℤ) V) :
    (∀ i : ℤ, i ∈ Finset.Icc 1 n → G (e i) = Sym2.mk (v (i - 1)) (v i)) ↔ (∀ i : ℤ, i ∈ Finset.Icc 1 n → G (e i) = Sym2.mk (v (i - 1)) (v i)) :=
  Iff.rfl

theorem def_euler_path {α β : Type*} [Nonempty α] [Nonempty β] (E : Set β) (V : Set α) (G : β → Sym2 α) [LeanBridges.Graphs.Multigraph V E G] (e : ℤ → β) (v : ℤ → α) (n : ℤ) (h1 : 0 ≤ n) (he : Set.MapsTo e (Set.Icc (1 : ℤ) n : Set ℤ) E) (hv : Set.MapsTo v (Set.Icc (0 : ℤ) n : Set ℤ) V) :
    ((∀ i : ℤ, i ∈ Finset.Icc 1 n → G (e i) = Sym2.mk (v (i - 1)) (v i)) ∧ Set.MapsTo e (Set.Icc (1 : ℤ) n : Set ℤ) E ∧ Set.InjOn e (Set.Icc (1 : ℤ) n : Set ℤ)) ∧ (∀ a ∈ E, ∃ i : ℤ, i ∈ Finset.Icc 1 n ∧ a = e i) ↔ ((∀ i : ℤ, i ∈ Finset.Icc 1 n → G (e i) = Sym2.mk (v (i - 1)) (v i)) ∧ Set.MapsTo e (Set.Icc (1 : ℤ) n : Set ℤ) E ∧ Set.InjOn e (Set.Icc (1 : ℤ) n : Set ℤ)) ∧ (∀ a ∈ E, ∃ i : ℤ, i ∈ Finset.Icc 1 n ∧ a = e i) :=
  Iff.rfl

theorem mun_walk_step {α β : Type*} [Nonempty α] [Nonempty β] (V : Set α) (E : Set β) (G : β → Sym2 α) [LeanBridges.Graphs.Multigraph V E G] (e : ℤ → β) (v : ℤ → α) (n : ℤ) (h1 : 0 ≤ n) (i : ℤ) (h2 : i ∈ Finset.Icc (1 : ℤ) n) (h3 : ∀ i : ℤ, i ∈ Finset.Icc 1 n → G (e i) = Sym2.mk (v (i - 1)) (v i)) (he : Set.MapsTo e (Set.Icc (1 : ℤ) n : Set ℤ) E) (hv : Set.MapsTo v (Set.Icc (0 : ℤ) n : Set ℤ) V) :
    G (e i) = Sym2.mk (v (i - 1)) (v i) :=
  LeanBridges.Graphs.walk_step V E G e v n h1 i h2 h3 he hv

theorem mun_joined_incident_1 {α β : Type*} [Nonempty α] [Nonempty β] (E : Set β) (V : Set α) (a : β) (u : α) (w : α) (G : β → Sym2 α) [LeanBridges.Graphs.Multigraph V E G] (h1 : a ∈ E) (h2 : u ∈ V) (h3 : w ∈ V) (h4 : G a = Sym2.mk u w) :
    u ∈ G a :=
  LeanBridges.Graphs.joined_incident_left E V a u w G h1 h2 h3 h4

theorem mun_joined_incident_2 {α β : Type*} [Nonempty α] [Nonempty β] (E : Set β) (V : Set α) (a : β) (u : α) (w : α) (G : β → Sym2 α) [LeanBridges.Graphs.Multigraph V E G] (h1 : a ∈ E) (h2 : u ∈ V) (h3 : w ∈ V) (h4 : G a = Sym2.mk u w) :
    w ∈ G a :=
  LeanBridges.Graphs.joined_incident_right E V a u w G h1 h2 h3 h4

theorem mun_walk_distinct {α β : Type*} [Nonempty α] [Nonempty β] (V : Set α) (E : Set β) (G : β → Sym2 α) [LeanBridges.Graphs.Multigraph V E G] (e : ℤ → β) (v : ℤ → α) (n : ℤ) (h1 : 0 ≤ n) (i : ℤ) (h2 : i ∈ Finset.Icc (1 : ℤ) n) (h3 : ∀ i : ℤ, i ∈ Finset.Icc 1 n → G (e i) = Sym2.mk (v (i - 1)) (v i)) (he : Set.MapsTo e (Set.Icc (1 : ℤ) n : Set ℤ) E) (hv : Set.MapsTo v (Set.Icc (0 : ℤ) n : Set ℤ) V) :
    ¬ v (i - 1) = v i :=
  LeanBridges.Graphs.walk_distinct V E G e v n h1 i h2 h3 he hv

theorem mun_incident_of_joined {α β : Type*} [Nonempty α] [Nonempty β] (V : Set α) (x : α) (E : Set β) (G : β → Sym2 α) [LeanBridges.Graphs.Multigraph V E G] (a : β) (u : α) (w : α) (h1 : x ∈ V) (h2 : G a = Sym2.mk u w) :
    x ∈ G a ↔ x = u ∨ x = w :=
  LeanBridges.Graphs.incident_of_joined V x E G a u w h1 h2

theorem mun_not_incident {α β : Type*} [Nonempty α] [Nonempty β] (E : Set β) (V : Set α) (a : β) (u : α) (w : α) (x : α) (G : β → Sym2 α) [LeanBridges.Graphs.Multigraph V E G] (h1 : a ∈ E) (h2 : u ∈ V) (h3 : w ∈ V) (h4 : x ∈ V) (h5 : G a = Sym2.mk u w) (h6 : ¬ x = u) (h7 : ¬ x = w) :
    ¬ x ∈ G a :=
  LeanBridges.Graphs.not_incident E V a u w x G h1 h2 h3 h4 h5 h6 h7

theorem mun_join_distinct {α β : Type*} [Nonempty α] [Nonempty β] (E : Set β) (V : Set α) (a : β) (u : α) (w : α) (G : β → Sym2 α) [LeanBridges.Graphs.Multigraph V E G] (h1 : a ∈ E) (h2 : u ∈ V) (h3 : w ∈ V) (h4 : G a = Sym2.mk u w) :
    ¬ u = w :=
  LeanBridges.Graphs.join_distinct E V a u w G h1 h2 h3 h4

theorem def_degree {α β : Type*} [Nonempty α] [Nonempty β] (E : Set β) (V : Set α) (x : α) (G : β → Sym2 α) [LeanBridges.Graphs.Multigraph V E G] (h1 : x ∈ V) :
    {a ∈ E | x ∈ G a}.encard = {a ∈ E | x ∈ G a}.encard :=
  rfl

end Parley.Items.Stdlib.Graphs
