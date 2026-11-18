module

public import Lean.Parser.Command
public import Mathlib.Data.Sym.Sym2
public import Mathlib.Data.Set.Function
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Data.Int.Interval

/-!
# Graphs

An undirected multigraph is the function sending each edge to its two
ends, `G : β → Sym2 α`, as set.mm's `iEdg` sends each edge's name to the
pair of its ends; its vertices are a set `V : Set α` and its edges a set
`E : Set β`. Two edges may have the same ends, which is what makes it a
multigraph, and no edge has one vertex for both ends. The page's other
notions of a graph, its degree, walks and Euler paths, are written out as
their definitions say.
-/

public section

namespace LeanBridges.Graphs

/-- `G` is an undirected multigraph with vertices `V` and edges `E`, set.mm's
`UMGraph`: each edge has its ends among the vertices, and two different
ones. -/
class Multigraph {α β : Type*} (V : Set α) (E : Set β) (G : β → Sym2 α) : Prop where
  ends_mem : ∀ a ∈ E, ∀ x ∈ G a, x ∈ V
  not_loop : ∀ a ∈ E, ¬ (G a).IsDiag

/-- `mun:stdlib/graphs/joined-incident`, its first sentence. -/
theorem joined_incident_left {α β : Type*} (E : Set β) (V : Set α) (a : β) (u : α) (w : α)
    (G : β → Sym2 α) [Multigraph V E G] (_h1 : a ∈ E) (_h2 : u ∈ V) (_h3 : w ∈ V)
    (h4 : G a = Sym2.mk u w) : u ∈ G a := by
  rw [h4]
  exact Sym2.mem_mk_left u w

/-- `mun:stdlib/graphs/joined-incident`, its second sentence. -/
theorem joined_incident_right {α β : Type*} (E : Set β) (V : Set α) (a : β) (u : α) (w : α)
    (G : β → Sym2 α) [Multigraph V E G] (_h1 : a ∈ E) (_h2 : u ∈ V) (_h3 : w ∈ V)
    (h4 : G a = Sym2.mk u w) : w ∈ G a := by
  rw [h4]
  exact Sym2.mem_mk_right u w

/-- `mun:stdlib/graphs/not-incident`. -/
theorem not_incident {α β : Type*} (E : Set β) (V : Set α) (a : β) (u : α) (w : α) (x : α)
    (G : β → Sym2 α) [Multigraph V E G] (_h1 : a ∈ E) (_h2 : u ∈ V) (_h3 : w ∈ V)
    (_h4 : x ∈ V) (h5 : G a = Sym2.mk u w) (h6 : ¬ x = u) (h7 : ¬ x = w) :
    ¬ x ∈ G a := by
  rw [h5, Sym2.mem_iff]
  rintro (h | h)
  · exact h6 h
  · exact h7 h

/-- `mun:stdlib/graphs/join-distinct`: an edge of a multigraph has two
different ends. -/
theorem join_distinct {α β : Type*} (E : Set β) (V : Set α) (a : β) (u : α) (w : α)
    (G : β → Sym2 α) [hG : Multigraph V E G] (h1 : a ∈ E) (_h2 : u ∈ V) (_h3 : w ∈ V)
    (h4 : G a = Sym2.mk u w) : ¬ u = w := by
  intro huw
  apply hG.not_loop a h1
  rw [h4, huw]
  exact Sym2.mk_isDiag_iff.mpr rfl

/-- `mun:stdlib/graphs/incident-of-joined`: the vertices incident with an
edge that joins u and w are u and w. -/
theorem incident_of_joined {α β : Type*} (V : Set α) (x : α) (E : Set β)
    (G : β → Sym2 α) [Multigraph V E G] (a : β) (u : α) (w : α) (_h1 : x ∈ V)
    (h2 : G a = Sym2.mk u w) : x ∈ G a ↔ x = u ∨ x = w := by
  rw [h2]
  exact Sym2.mem_iff

/-- `mun:stdlib/graphs/walk-step`: the edge at each place of a walk joins
the vertices on either side of it. -/
theorem walk_step {α β : Type*} (V : Set α) (E : Set β)
    (G : β → Sym2 α) [Multigraph V E G] (e : ℤ → β) (v : ℤ → α) (n : ℤ) (_h1 : 0 ≤ n)
    (i : ℤ) (h2 : i ∈ Finset.Icc (1 : ℤ) n)
    (h3 : ∀ i : ℤ, i ∈ Finset.Icc 1 n → G (e i) = Sym2.mk (v (i - 1)) (v i))
    (_he : Set.MapsTo e (Set.Icc (1 : ℤ) n : Set ℤ) E)
    (_hv : Set.MapsTo v (Set.Icc (0 : ℤ) n : Set ℤ) V) :
    G (e i) = Sym2.mk (v (i - 1)) (v i) :=
  h3 i h2

/-- `mun:stdlib/graphs/walk-distinct`: a walk never stays where it is, as an
edge of a multigraph has two different ends. -/
theorem walk_distinct {α β : Type*} (V : Set α) (E : Set β)
    (G : β → Sym2 α) [hG : Multigraph V E G] (e : ℤ → β) (v : ℤ → α) (n : ℤ) (_h1 : 0 ≤ n)
    (i : ℤ) (h2 : i ∈ Finset.Icc (1 : ℤ) n)
    (h3 : ∀ i : ℤ, i ∈ Finset.Icc 1 n → G (e i) = Sym2.mk (v (i - 1)) (v i))
    (he : Set.MapsTo e (Set.Icc (1 : ℤ) n : Set ℤ) E)
    (_hv : Set.MapsTo v (Set.Icc (0 : ℤ) n : Set ℤ) V) :
    ¬ v (i - 1) = v i := by
  intro h
  apply hG.not_loop (e i) (he (Finset.mem_Icc.mp h2))
  rw [h3 i h2, h]
  exact Sym2.mk_isDiag_iff.mpr rfl

end LeanBridges.Graphs
