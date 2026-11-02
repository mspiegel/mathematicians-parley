module

public import LeanBridges

/-! Written from corpus/stdlib/functions.records by parley build lean. -/

public section

namespace Parley.Items.Stdlib.Functions

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

end Parley.Items.Stdlib.Functions
