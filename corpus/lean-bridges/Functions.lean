module

public import Mathlib

/-!
# Functions

What the library says of functions, each item said in
Lean as the build writes it.
-/

public section

namespace LeanBridges.Functions

/-- g⁻¹(y) of a map g on A: the x in A that g sends to y, where there is
one, and y itself where there is none. Mathlib's `Function.invFunOn` asks
`[Nonempty α]`, which a statement over sets does not carry; what g⁻¹ gives
off g's image is never used, as set.mm's converse leaves it unsaid. -/
noncomputable def inverse {α : Type*} (g : α → α) (A : Set α) (y : α) : α := by
  classical
  exact if h : ∃ x ∈ A, g x = y then h.choose else y

/-- g⁻¹ undoes a one-to-one g on its domain. -/
theorem inverse_of_value {α : Type*} (g : α → α) (A : Set α) (x : α)
    (hg : Set.InjOn g A) (hx : x ∈ A) : inverse g A (g x) = x := by
  classical
  have h : ∃ y ∈ A, g y = g x := ⟨x, hx, rfl⟩
  unfold inverse
  simp only [h, ↓reduceDIte]
  exact hg h.choose_spec.1 hx h.choose_spec.2

/-- `def:stdlib/functions/image`. -/
theorem image {α β : Type*} (X : Set α) (Y : Set α) (f : α → β) (u : β) (W : Set β) (h1 : Y ⊆ X) (_hf : Set.MapsTo f X W) :
    u ∈ f '' (X ∩ Y) ↔ (∃ s ∈ Y, u = f s) :=
  ⟨fun ⟨s, ⟨_, hs⟩, e⟩ => ⟨s, hs, e.symm⟩, fun ⟨s, hs, e⟩ => ⟨s, ⟨h1 hs, hs⟩, e.symm⟩⟩

/-- `def:stdlib/functions/set-image`. -/
theorem set_image {α β : Type*} (E : α → β) (Y : Set α) (u : β) (Z : Set β) (hE : Set.MapsTo E Y Z) :
    u ∈ (fun s : α => E s) '' Y ↔ (∃ s ∈ Y, u = E s) :=
  ⟨fun ⟨s, hs, e⟩ => ⟨s, hs, e.symm⟩, fun ⟨s, hs, e⟩ => ⟨s, hs, e.symm⟩⟩

/-- `def:stdlib/functions/onto`. -/
theorem onto {α β : Type*} (X : Set α) (Y : Set β) (f : α → β) (hf : Set.MapsTo f X Y) :
    Set.MapsTo f X Y ∧ Set.SurjOn f X Y ↔ Set.MapsTo f X Y ∧ (∀ y ∈ Y, ∃ x ∈ X, y = f x) :=
  and_congr_right fun _ => ⟨fun h y hy => let ⟨x, hx, e⟩ := h hy; ⟨x, hx, e.symm⟩, fun h y hy => let ⟨x, hx, e⟩ := h y hy; ⟨x, hx, e.symm⟩⟩

/-- `def:stdlib/functions/one-to-one-onto`. -/
theorem one_to_one_onto {α β : Type*} (X : Set α) (Y : Set β) (f : α → β) (hf : Set.MapsTo f X Y) :
    Set.MapsTo f X Y ∧ Set.InjOn f X ∧ Set.SurjOn f X Y ↔ (Set.MapsTo f X Y ∧ Set.InjOn f X) ∧ Set.MapsTo f X Y ∧ Set.SurjOn f X Y :=
  ⟨fun ⟨a, b, c⟩ => ⟨⟨a, b⟩, a, c⟩, fun ⟨⟨a, b⟩, _, c⟩ => ⟨a, b, c⟩⟩

end LeanBridges.Functions
