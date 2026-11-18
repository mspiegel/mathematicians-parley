module

public import Graphs
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Data.Sym.Sym2
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Graphs

/-! Written from tests/stdlib/graphs.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Graphs.Walk

theorem walk {α β : Type*} [Nonempty α] [Nonempty β] (V : Set α) (E : Set β) (G : β → Sym2 α) [LeanBridges.Graphs.Multigraph V E G] (n : ℤ) (hH2 : 0 ≤ n) (e : ℤ → β) (hH3 : Set.MapsTo e (Set.Icc (1 : ℤ) n : Set ℤ) E) (v : ℤ → α) (hH4 : Set.MapsTo v (Set.Icc (0 : ℤ) n : Set ℤ) V) (hH5 : ∀ i : ℤ, i ∈ Finset.Icc 1 n → G (e i) = Sym2.mk (v (i - 1)) (v i)) :
    (∀ i : ℤ, i ∈ Finset.Icc 1 n → G (e i) = Sym2.mk (v (i - 1)) (v i)) := by
  -- 1. def:graphs-walk, from H5
  exact ((Parley.Items.Stdlib.Graphs.def_walk (V := V) (E := E) (G := G) (e := e) (v := v) (n := n) hH2 hH3 hH4)).mpr hH5

end Parley.Tests.Stdlib.Graphs.Walk
