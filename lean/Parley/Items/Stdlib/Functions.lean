module

public import Functions
public import Tactics

/-! Written from corpus/stdlib/functions.records by parley build lean. -/

public section

namespace Parley.Items.Stdlib.Functions

theorem def_set_image {α β : Type*} (E : α → β) (Y : Set α) (u : β) (Z : Set β) (hE : Set.MapsTo E Y Z) :
    u ∈ (fun s : α => E s) '' Y ↔ (∃ s ∈ Y, u = E s) :=
  LeanBridges.Functions.set_image E Y u Z hE

theorem mun_function_value {α β : Type*} (D : Set α) (E : Set β) (f : α → β) (x : α) (hf : Set.MapsTo f D E) (h1 : x ∈ D) :
    f x ∈ E :=
  hf h1

theorem def_image {α β : Type*} (X : Set α) (Y : Set α) (f : α → β) (u : β) (W : Set β) (hf : Set.MapsTo f X W) (h1 : Y ⊆ X) :
    u ∈ f '' (X ∩ Y) ↔ (∃ s ∈ Y, u = f s) :=
  LeanBridges.Functions.image X Y f u W hf h1

theorem mun_image_within {α β : Type*} (W : Set β) (Y : Set α) (f : α → β) (X : Set α) (hf : Set.MapsTo f X W) :
    f '' (X ∩ Y) ⊆ W :=
  (hf.mono_left Set.inter_subset_left).image_subset

theorem mun_image_monotone {α β : Type*} (Y : Set α) (Z : Set α) (f : α → β) (X : Set α) (W : Set β) (hf : Set.MapsTo f X W) (h1 : Y ⊆ Z) :
    f '' (X ∩ Y) ⊆ f '' (X ∩ Z) :=
  Set.image_mono (Set.inter_subset_inter_right X h1)

theorem mun_function_into {α β : Type*} (E : α → β) (X : Set α) (Y : Set β) (h1 : True) (h2 : ∀ x ∈ X, E x ∈ Y) :
    Set.MapsTo E X Y :=
  fun x hx => h2 x hx

theorem mun_value_in_image {α β : Type*} (X : Set α) (Y : Set α) (f : α → β) (s : α) (W : Set β) (hf : Set.MapsTo f X W) (h1 : Y ⊆ X) (h2 : s ∈ Y) :
    f s ∈ f '' (X ∩ Y) :=
  Set.mem_image_of_mem f ⟨h1 h2, h2⟩

theorem def_one_to_one {α β : Type*} (X : Set α) (Y : Set β) (f : α → β) (hf : Set.MapsTo f X Y) :
    Set.MapsTo f X Y ∧ Set.InjOn f X ↔ Set.MapsTo f X Y ∧ (∀ s ∈ X, ∀ t ∈ X, f s = f t → s = t) :=
  Iff.rfl

theorem def_onto {α β : Type*} (X : Set α) (Y : Set β) (f : α → β) (hf : Set.MapsTo f X Y) :
    Set.MapsTo f X Y ∧ Set.SurjOn f X Y ↔ Set.MapsTo f X Y ∧ (∀ y ∈ Y, ∃ x ∈ X, y = f x) :=
  LeanBridges.Functions.onto X Y f hf

theorem def_one_to_one_onto {α β : Type*} (X : Set α) (Y : Set β) (f : α → β) (hf : Set.MapsTo f X Y) :
    Set.MapsTo f X Y ∧ Set.InjOn f X ∧ Set.SurjOn f X Y ↔ (Set.MapsTo f X Y ∧ Set.InjOn f X) ∧ Set.MapsTo f X Y ∧ Set.SurjOn f X Y :=
  LeanBridges.Functions.one_to_one_onto X Y f hf

theorem mun_inverse_value {α : Type*} (X : Set α) (Y : Set α) (g : α → α) (y : α) (h1 : Set.MapsTo g Y X ∧ Set.InjOn g Y) (h2 : y ∈ Y) :
    LeanBridges.Functions.inverse g Y (g y) = y :=
  LeanBridges.Functions.inverse_of_value g Y y h1.2 h2

theorem def_preimage {α β : Type*} (X : Set α) (Z : Set β) (f : α → β) (u : α) (W : Set β) (hf : Set.MapsTo f X W) :
    u ∈ X ∩ f ⁻¹' Z ↔ u ∈ X ∧ f u ∈ Z :=
  Iff.rfl

theorem mun_preimage_within {α β : Type*} (X : Set α) (Z : Set β) (f : α → β) (W : Set β) (hf : Set.MapsTo f X W) :
    X ∩ f ⁻¹' Z ⊆ X :=
  Set.inter_subset_left

theorem mun_composition_value {α β γ : Type*} (X : Set α) (f : α → β) (g : β → γ) (x : α) (Y : Set β) (hf : Set.MapsTo f X Y) (W : Set γ) (hg : Set.MapsTo g Y W) (h1 : x ∈ X) :
    (g ∘ f) x = g (f x) :=
  rfl

end Parley.Items.Stdlib.Functions
