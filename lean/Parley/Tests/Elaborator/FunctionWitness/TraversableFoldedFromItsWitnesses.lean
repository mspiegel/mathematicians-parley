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

/-! Written from tests/elaborator/function-witness.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.FunctionWitness.TraversableFoldedFromItsWitnesses

theorem traversable_folded_from_its_witnesses {α β : Type*} [Nonempty α] [Nonempty β] (V : Set α) (E : Set β) (G : β → Sym2 α) [LeanBridges.Graphs.Multigraph V E G] (hR1 : ∃ n : ℤ, 0 ≤ n ∧ (∃ e : ℤ → β, Set.MapsTo e (Set.Icc (1 : ℤ) n : Set ℤ) E ∧ (∃ v : ℤ → α, Set.MapsTo v (Set.Icc (0 : ℤ) n : Set ℤ) V ∧ (((∀ i : ℤ, i ∈ Finset.Icc 1 n → G (e i) = Sym2.mk (v (i - 1)) (v i)) ∧ Set.MapsTo e (Set.Icc (1 : ℤ) n : Set ℤ) E ∧ Set.InjOn e (Set.Icc (1 : ℤ) n : Set ℤ)) ∧ (∀ a ∈ E, ∃ i : ℤ, i ∈ Finset.Icc 1 n ∧ a = e i))))) :
    (∃ n : ℤ, 0 ≤ n ∧ (∃ e : ℤ → β, Set.MapsTo e (Set.Icc (1 : ℤ) n : Set ℤ) E ∧ (∃ v : ℤ → α, Set.MapsTo v (Set.Icc (0 : ℤ) n : Set ℤ) V ∧ (((∀ i : ℤ, i ∈ Finset.Icc 1 n → G (e i) = Sym2.mk (v (i - 1)) (v i)) ∧ Set.MapsTo e (Set.Icc (1 : ℤ) n : Set ℤ) E ∧ Set.InjOn e (Set.Icc (1 : ℤ) n : Set ℤ)) ∧ (∀ a ∈ E, ∃ i : ℤ, i ∈ Finset.Icc 1 n ∧ a = e i))))) := by
  -- 1. obtain n, e, v from R1
  obtain ⟨n, s1a, e, s1b, v, s1c, s1d⟩ := hR1
  -- 2. def:traversable, from 1
  exact ((Parley.Items.Stdlib.Graphs.def_traversable (E := E) (V := V) (G := G))).mpr ⟨n, s1a, e, s1b, v, s1c, s1d⟩

end Parley.Tests.Elaborator.FunctionWitness.TraversableFoldedFromItsWitnesses
