module

public import Lean.Parser.Command
public import Mathlib.Algebra.Group.Subgroup.Defs

/-!
# Groups

What the library says of groups, each item said in
Lean as the build writes it.
-/

public section

namespace LeanBridges.Groups

/-- `def:stdlib/groups/coset`. -/
theorem coset {G : Type*} [Group G] (g : G) (u : G) (H : Subgroup G) (h2 : g ∈ (Set.univ : Set G)) :
    u ∈ (g * ·) '' (H : Set G) ↔ (∃ h ∈ (H : Set G), u = g * h) :=
  ⟨fun ⟨h, hh, e⟩ => ⟨h, hh, e.symm⟩, fun ⟨h, hh, e⟩ => ⟨h, hh, e.symm⟩⟩

end LeanBridges.Groups
