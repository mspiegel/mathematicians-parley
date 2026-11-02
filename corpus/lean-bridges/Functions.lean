module

public import Mathlib
public import Counting

/-!
# Functions

What the library says of functions, each item said in
Lean as the build writes it.
-/

public section

namespace LeanBridges.Functions

/-- `def:stdlib/functions/image`. -/
theorem image {α : Type*} (X : Set α) (Y : Set α) (f : α → α) (u : α) (W : Set α) (hf : Set.MapsTo f X W) (h1 : Y ⊆ X) :
    u ∈ f '' Y ↔ (∃ s ∈ Y, u = f s) :=
  ⟨fun ⟨s, hs, e⟩ => ⟨s, hs, e.symm⟩, fun ⟨s, hs, e⟩ => ⟨s, hs, e.symm⟩⟩

end LeanBridges.Functions
