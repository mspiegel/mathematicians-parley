module

public import SetTactics
public import Tactics
public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/halmos/empty-set-unique.proof by parley build lean. -/

public section

namespace Parley.Proofs.Halmos.EmptySetUnique.EmptySetUnique

theorem empty_set_unique {α : Type*} (A : Set α) (hH2 : ¬ (∃ a ∈ A, True)) :
    A = ∅ := by
  -- 1. proof
  have s1 : ∀ x ∈ A, x ∈ (∅ : Set α) := by
    intro x hK
    -- 1.1. exhibit, from K
    have s1_1 : ∃ a ∈ A, True := ⟨x, by parley_set_side, trivial⟩
    -- 1.2. restate H2
    have s1_2 : ¬ (∃ a ∈ A, True) := by parley_set_side
    exact absurd s1_1 s1_2
  -- 2. mun:empty-subset X := A
  have s2 : ∅ ⊆ A := by exact (Parley.Items.Stdlib.Sets.mun_empty_subset (X := A))
  -- 3. def:subset X := ∅, Y := A, from 2
  have s3 : ∀ x ∈ (∅ : Set α), x ∈ A := ((Parley.Items.Stdlib.Sets.def_subset (X := ∅) (Y := A))).mp s2
  -- 4. axi:extensionality X := A, Y := ∅, from 1, 3
  exact (Parley.Items.Stdlib.Sets.axi_extensionality (X := A) (Y := ∅) s1 s3)

end Parley.Proofs.Halmos.EmptySetUnique.EmptySetUnique
