module

public import Functions
public import SetTactics
public import SubstTactics
public import Tactics
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Functions
public import Parley.Proofs.Setmm.ValueOfOnto.ValueOfOnto

/-! Written from proofs/setmm/inverse-lands-in-domain.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.InverseLandsInDomain.InverseLandsInDomain

theorem inverse_lands_in_domain {α : Type*} (A : Set α) (B : Set α) (F : α → α) (hH3 : Set.MapsTo F A B ∧ Set.InjOn F A) (hH4 : F '' (A ∩ A) = B) (C : α) (hH5 : C ∈ B) :
    LeanBridges.Functions.inverse F A C ∈ A := by
  -- 1. obtain x: thm:value-of-onto y := C, from H4, H5
  obtain ⟨x, s1a, s1b⟩ := (Parley.Proofs.Setmm.ValueOfOnto.ValueOfOnto.value_of_onto (A := A) (B := B) (F := F) (by parley_set_side) hH4 (y := C) hH5)
  -- 2. mun:inverse-value g := F, y := x, from H3, 1
  have s2 : LeanBridges.Functions.inverse F A (F x) = x := by exact (Parley.Items.Stdlib.Functions.mun_inverse_value (X := B) (Y := A) (g := F) (y := x) hH3 s1a)
  -- 3. substitute C = F(x) (line 1) into line 2
  have s3 : LeanBridges.Functions.inverse F A C = x := by parley_subst_at s1b s2
  -- 4. substitute F⁻¹(C) = x (line 3) into line 1
  have s4 : LeanBridges.Functions.inverse F A C ∈ A := by parley_subst_at s3 s1a
  all_goals exact s4

end Parley.Proofs.Setmm.InverseLandsInDomain.InverseLandsInDomain
