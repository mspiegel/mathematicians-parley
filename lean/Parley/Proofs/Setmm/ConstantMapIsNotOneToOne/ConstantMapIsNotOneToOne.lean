module

public import SetTactics
public import Tactics
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Functions
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/setmm/constant-map-is-not-one-to-one.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.ConstantMapIsNotOneToOne.ConstantMapIsNotOneToOne

theorem constant_map_is_not_one_to_one {α : Type*} (A : Set α) (C : Set α) (B : α) (F : α → α) (hH4 : Set.MapsTo F A ({B} : Set α)) (X : α) (hH5 : X ∈ A) (Y : α) (hH6 : Y ∈ A) (hH7 : ¬ X = Y) :
    ¬ (Set.MapsTo F A C ∧ Set.InjOn F A) := by
  -- 1. mun:function-value f := F, x := X, from H5
  have s1 : F X ∈ ({B} : Set α) := by exact (Parley.Items.Stdlib.Functions.mun_function_value (D := A) (E := ({B} : Set α)) (f := F) (x := X) hH5 (by parley_set_side))
  -- 2. mun:function-value f := F, x := Y, from H6
  have s2 : F Y ∈ ({B} : Set α) := by exact (Parley.Items.Stdlib.Functions.mun_function_value (D := A) (E := ({B} : Set α)) (f := F) (x := Y) hH6 (by parley_set_side))
  -- 3. calculation
  have s3 : F X = F Y := by
    calc F X = B := ((Parley.Items.Stdlib.Sets.def_singleton (a := B) (x := F X))).mp s1
      _ = F Y := (((Parley.Items.Stdlib.Sets.def_singleton (a := B) (x := F Y))).mp s2).symm
  -- 4. contradiction
  intro hS
  -- 4.1. def:one-to-one f := F, X := A, Y := C, from S
  have s4_1a : Set.MapsTo F A C := (((Parley.Items.Stdlib.Functions.def_one_to_one (X := A) (Y := C) (f := F) (by parley_set_side))).mp hS).1
  have s4_1b : ∀ s ∈ A, ∀ t ∈ A, F s = F t → s = t := (((Parley.Items.Stdlib.Functions.def_one_to_one (X := A) (Y := C) (f := F) (by parley_set_side))).mp hS).2
  -- 4.2. instantiate s := X, t := Y in line 4.1, from H5, H6, 3
  have s4_2 : X = Y := by first | exact (s4_1b X (by parley_set_side) Y (by parley_set_side) (by parley_set_side)) | exact ((s4_1b X (by parley_set_side) Y (by parley_set_side) (by parley_set_side))).symm | simpa using (s4_1b X (by parley_set_side) Y (by parley_set_side) (by parley_set_side)) | exact_mod_cast (s4_1b X (by parley_set_side) Y (by parley_set_side) (by parley_set_side)) | (have h := (s4_1b X (by parley_set_side) Y (by parley_set_side) (by parley_set_side)); parley_set_side)
  -- 4.3. restate H7
  have s4_3 : ¬ X = Y := by parley_set_side
  exact s4_3 s4_2

end Parley.Proofs.Setmm.ConstantMapIsNotOneToOne.ConstantMapIsNotOneToOne
