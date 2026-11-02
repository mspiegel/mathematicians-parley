module

public import LeanBridges
public import Parley.Items.Stdlib.Functions

/-! Written from tests/elaborator/a-set-image-from-an-equation.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ASetImageFromAnEquation.ASetImageFromAnEquation

theorem a_set_image_from_an_equation (m : ℤ) (t : ℤ) (hH3 : t = 2 * m) :
    t ∈ (fun n : ℤ => 2 * n) '' (Set.univ : Set ℤ) := by
  -- 1. def:set-image u := t, from H3
  have s1 : t ∈ (fun n : ℤ => 2 * n) '' (Set.univ : Set ℤ) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Functions.def_set_image (E := (fun n : ℤ => 2 * n)) (Y := (Set.univ : Set ℤ)) (u := t) (Z := Set.univ) (by parley_side))).mpr ⟨m, by parley_side, by parley_side⟩ | (have h := ((Parley.Items.Stdlib.Functions.def_set_image (E := (fun n : ℤ => 2 * n)) (Y := (Set.univ : Set ℤ)) (u := t) (Z := Set.univ) (by parley_side))).mpr ⟨m, by parley_side, by parley_side⟩; parley_side)
  all_goals parley_side

end Parley.Tests.Elaborator.ASetImageFromAnEquation.ASetImageFromAnEquation
