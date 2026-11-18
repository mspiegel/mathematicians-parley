module

public import Graphs
public import Sets
public import Batteries.Util.ExtendedBinder
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Sym.Sym2
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.TypeStar

/-! Written from tests/elaborator/inspection.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.Inspection.ListedProperty

theorem listed_property {α β : Type*} [Nonempty α] [Nonempty β] (V : Set α) (E : Set β) (G : β → Sym2 α) [LeanBridges.Graphs.Multigraph V E G] (A : α) (B : α) (C : α) (D : α) (b₁ : β) (b₂ : β) (hH1a : V = ({A, B, C, D} : Set α)) (hH1b : E = ({b₁, b₂} : Set β)) (hH1c : ¬ A = B) (hH1d : ¬ A = C) (hH1e : ¬ A = D) (hH1f : ¬ B = C) (hH1g : ¬ B = D) (hH1h : ¬ C = D) (hH1i : ¬ b₁ = b₂) (hH1j : G b₁ = Sym2.mk A B) (hH1k : G b₂ = Sym2.mk A C) :
    {x ∈ E | A ∈ G x} = ({b₁, b₂} : Set β) := by
  -- 1. inspection, from H1
  rw [hH1b]; simp only [LeanBridges.Sets.sep_insert_of (p := (fun x : β => A ∈ G x)) (show A ∈ G b₁ by simp [hH1a, hH1b, hH1c, Ne.symm hH1c, hH1d, Ne.symm hH1d, hH1e, Ne.symm hH1e, hH1f, Ne.symm hH1f, hH1g, Ne.symm hH1g, hH1h, Ne.symm hH1h, hH1i, Ne.symm hH1i, hH1j, hH1k, Sym2.mem_iff]), LeanBridges.Sets.sep_singleton_of (p := (fun x : β => A ∈ G x)) (show A ∈ G b₂ by simp [hH1a, hH1b, hH1c, Ne.symm hH1c, hH1d, Ne.symm hH1d, hH1e, Ne.symm hH1e, hH1f, Ne.symm hH1f, hH1g, Ne.symm hH1g, hH1h, Ne.symm hH1h, hH1i, Ne.symm hH1i, hH1j, hH1k, Sym2.mem_iff])]

end Parley.Tests.Elaborator.Inspection.ListedProperty
