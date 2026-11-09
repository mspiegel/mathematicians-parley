module

public import SetTactics
public import Tactics
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Functions
public import Parley.Items.Stdlib.Reasoning

/-! Written from proofs/setmm/one-to-one-values.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.OneToOneValues.OneToOneValues

theorem one_to_one_values {α : Type*} (A : Set α) (B : Set α) (F : α → α) (hH3 : Set.MapsTo F A B ∧ Set.InjOn F A) (C : α) (hH4 : C ∈ A) (D : α) (hH5 : D ∈ A) (hH6 : F C = F D) :
    C = D := by
  -- 1. def:one-to-one, from H3
  have s1 : ∀ s ∈ A, ∀ t ∈ A, F s = F t → s = t := (((Parley.Items.Stdlib.Functions.def_one_to_one (X := A) (Y := B) (f := F) (by parley_set_side))).mp hH3).2
  -- 2. instantiate s := C, t := D in line 1, from H4, H5
  have s2 : F C = F D → C = D := by first | exact (s1 C (by parley_set_side) D (by parley_set_side)) | exact ((s1 C (by parley_set_side) D (by parley_set_side))).symm | simpa using (s1 C (by parley_set_side) D (by parley_set_side)) | exact_mod_cast (s1 C (by parley_set_side) D (by parley_set_side)) | (have h := (s1 C (by parley_set_side) D (by parley_set_side)); parley_set_side)
  -- 3. mun:modus-ponens, from H6, 2
  exact (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := F C = F D) (Q := C = D) s2 hH6)

end Parley.Proofs.Setmm.OneToOneValues.OneToOneValues
