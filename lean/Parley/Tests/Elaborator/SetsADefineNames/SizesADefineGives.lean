module

public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Function
public import Mathlib.Data.Set.Operations
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Set
public import Mathlib.Tactic.SetNotationForOrder
public import Parley.Items.Stdlib.Functions
public import Parley.Items.Stdlib.Sets

/-! Written from tests/elaborator/sets-a-define-names.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.SetsADefineNames.SizesADefineGives

theorem sizes_a_define_gives (N : ℤ) (hH1 : 0 < N) (hH2 : N ∈ Finset.Icc (1 : ℤ) N) :
    (∃ x ∈ 𝒫 (Set.Icc (1 : ℤ) N : Set ℤ), (({N} : Set ℤ).ncard : ℤ) = (x.ncard : ℤ)) := by
  set I : ℤ → Set ℤ := fun k : ℤ => (fun x : Set ℤ => (x.ncard : ℤ)) '' (𝒫 (Set.Icc (1 : ℤ) k : Set ℤ)) with hD1
  -- 1. mun:singleton-subset, from H2
  have s1 : ({N} : Set ℤ) ⊆ (Set.Icc (1 : ℤ) N : Set ℤ) := by exact (Parley.Items.Stdlib.Sets.mun_singleton_subset (X := (Set.Icc (1 : ℤ) N : Set ℤ)) (a := N) (by simpa only [Finset.mem_Icc, Set.mem_Icc] using hH2))
  -- 2. def:powerset S := {N}, from 1
  have s2 : ({N} : Set ℤ) ⊆ (Set.Icc (1 : ℤ) N : Set ℤ) := ((Parley.Items.Stdlib.Sets.def_powerset (A := (Set.Icc (1 : ℤ) N : Set ℤ)) (S := ({N} : Set ℤ)))).mpr s1
  -- 3. exhibit, from 2
  have s3 : ∃ x ∈ 𝒫 (Set.Icc (1 : ℤ) N : Set ℤ), (({N} : Set ℤ).ncard : ℤ) = (x.ncard : ℤ) := ⟨({N} : Set ℤ), s2, rfl⟩
  -- 4. def:set-image u := |{N}|, from D1, H2, 3
  have s4 : (({N} : Set ℤ).ncard : ℤ) ∈ I N := ((Parley.Items.Stdlib.Functions.def_set_image (E := (fun x : Set ℤ => (x.ncard : ℤ))) (Y := 𝒫 (Set.Icc (1 : ℤ) N : Set ℤ)) (u := (({N} : Set ℤ).ncard : ℤ)) (Z := Set.univ) (Set.mapsTo_univ _ _))).mpr s3
  -- 5. def:set-image, from D1, H2, 4
  exact ((Parley.Items.Stdlib.Functions.def_set_image (E := (fun x : Set ℤ => (x.ncard : ℤ))) (Y := 𝒫 (Set.Icc (1 : ℤ) N : Set ℤ)) (u := (({N} : Set ℤ).ncard : ℤ)) (Z := Set.univ) (Set.mapsTo_univ _ _))).mp s4

end Parley.Tests.Elaborator.SetsADefineNames.SizesADefineGives
