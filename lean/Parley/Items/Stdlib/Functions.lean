module

public import LeanBridges

/-! Written from corpus/stdlib/functions.records by parley build lean. -/

public section

namespace Parley.Items.Stdlib.Functions

theorem def_set_image {α : Type*} (E : α → α) (Y : Set α) (u : α) (Z : Set α) (hE : Set.MapsTo E Y Z) :
    u ∈ (fun s : α => E s) '' Y ↔ (∃ s ∈ Y, u = E s) :=
  LeanBridges.Functions.set_image E Y u Z hE

theorem mun_function_value {α : Type*} (D : Set α) (E : Set α) (f : α → α) (x : α) (hf : Set.MapsTo f D E) (h1 : x ∈ D) :
    f x ∈ E :=
  hf h1

theorem def_image {α : Type*} (X : Set α) (Y : Set α) (f : α → α) (u : α) (W : Set α) (hf : Set.MapsTo f X W) (h1 : Y ⊆ X) :
    u ∈ f '' Y ↔ (∃ s ∈ Y, u = f s) :=
  LeanBridges.Functions.image X Y f u W hf h1

theorem mun_image_monotone {α : Type*} (Y : Set α) (Z : Set α) (f : α → α) (X : Set α) (W : Set α) (hf : Set.MapsTo f X W) (h1 : Y ⊆ Z) :
    f '' Y ⊆ f '' Z :=
  Set.image_mono h1

theorem mun_value_in_image {α : Type*} (X : Set α) (Y : Set α) (f : α → α) (s : α) (W : Set α) (hf : Set.MapsTo f X W) (h1 : Y ⊆ X) (h2 : s ∈ Y) :
    f s ∈ f '' Y :=
  Set.mem_image_of_mem f h2

theorem def_one_to_one {α : Type*} (X : Set α) (Y : Set α) (f : α → α) (hf : Set.MapsTo f X Y) :
    Set.MapsTo f X Y ∧ Set.InjOn f X ↔ Set.MapsTo f X Y ∧ (∀ s ∈ X, ∀ t ∈ X, f s = f t → s = t) :=
  Iff.rfl

theorem def_onto {α : Type*} (X : Set α) (Y : Set α) (f : α → α) (hf : Set.MapsTo f X Y) :
    Set.MapsTo f X Y ∧ Set.SurjOn f X Y ↔ Set.MapsTo f X Y ∧ (∀ y ∈ Y, ∃ x ∈ X, y = f x) :=
  LeanBridges.Functions.onto X Y f hf

theorem def_one_to_one_onto {α : Type*} (X : Set α) (Y : Set α) (f : α → α) (hf : Set.MapsTo f X Y) :
    Set.MapsTo f X Y ∧ Set.InjOn f X ∧ Set.SurjOn f X Y ↔ (Set.MapsTo f X Y ∧ Set.InjOn f X) ∧ Set.MapsTo f X Y ∧ Set.SurjOn f X Y :=
  LeanBridges.Functions.one_to_one_onto X Y f hf

theorem mun_inverse_value {α : Type*} (X : Set α) (Y : Set α) (g : α → α) (y : α) (h1 : Set.MapsTo g Y X ∧ Set.InjOn g Y) (h2 : y ∈ Y) :
    LeanBridges.Functions.inverse g Y (g y) = y :=
  LeanBridges.Functions.inverse_of_value g Y y h1.2 h2

theorem def_preimage {α : Type*} (X : Set α) (Z : Set α) (f : α → α) (u : α) (W : Set α) (hf : Set.MapsTo f X W) :
    u ∈ X ∩ f ⁻¹' Z ↔ u ∈ X ∧ f u ∈ Z :=
  Iff.rfl

theorem mun_preimage_within {α : Type*} (X : Set α) (Z : Set α) (f : α → α) (W : Set α) (hf : Set.MapsTo f X W) :
    X ∩ f ⁻¹' Z ⊆ X :=
  Set.inter_subset_left

end Parley.Items.Stdlib.Functions
