module

public import SetTactics
public import Tactics
public import WholeTactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Functions

/-! Written from tests/elaborator/a-set-image-from-an-equation.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ASetImageFromAnEquation.ASetImageFromAnEquation

theorem a_set_image_from_an_equation (m : ℤ) (t : ℤ) (hH3 : t = 2 * m) :
    t ∈ (fun n : ℤ => 2 * n) '' (Set.univ : Set ℤ) := by
  -- 1. def:set-image u := t, from H3
  first | (assumption; done) | exact ((Parley.Items.Stdlib.Functions.def_set_image (E := (fun n : ℤ => 2 * n)) (Y := (Set.univ : Set ℤ)) (u := t) (Z := Set.univ) (by parley_whole_side))).mpr ⟨m, by parley_set_side, by parley_set_side⟩ | (have h := ((Parley.Items.Stdlib.Functions.def_set_image (E := (fun n : ℤ => 2 * n)) (Y := (Set.univ : Set ℤ)) (u := t) (Z := Set.univ) (by parley_whole_side))).mpr ⟨m, by parley_set_side, by parley_set_side⟩; parley_set_side)

end Parley.Tests.Elaborator.ASetImageFromAnEquation.ASetImageFromAnEquation
