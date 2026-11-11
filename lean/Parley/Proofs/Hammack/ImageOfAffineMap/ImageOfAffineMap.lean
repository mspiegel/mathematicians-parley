module

public import NormTactics
public import SetTactics
public import Tactics
public import WholeTactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.SetNotationForOrder
public import Parley.Items.Stdlib.Functions
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/hammack/image-of-affine-map.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.ImageOfAffineMap.ImageOfAffineMap

set_option maxHeartbeats 400000 in
theorem image_of_affine_map (f : ℤ → ℤ) (hH2 : ∀ x : ℤ, f x = 4 * x + 5) :
    f '' ((Set.univ : Set ℤ) ∩ (Set.univ : Set ℤ)) = (fun k : ℤ => 4 * k + 1) '' (Set.univ : Set ℤ) := by
  -- 1. mun:subset-self
  have s1 : (Set.univ : Set ℤ) ⊆ (Set.univ : Set ℤ) := by exact (Parley.Items.Stdlib.Sets.mun_subset_self (X := (Set.univ : Set ℤ)))
  -- 2. proof
  have s2 : ∀ y ∈ f '' ((Set.univ : Set ℤ) ∩ (Set.univ : Set ℤ)), y ∈ (fun k : ℤ => 4 * k + 1) '' (Set.univ : Set ℤ) := by
    intro y hK1
    -- 2.1. obtain s: def:image u := y, Y := ℤ, from K1, 1
    obtain ⟨s, _, s2_1⟩ := ((Parley.Items.Stdlib.Functions.def_image (X := (Set.univ : Set ℤ)) (Y := (Set.univ : Set ℤ)) (f := f) (u := y) (W := Set.univ) (by parley_whole_side) (by parley_whole_side))).mp hK1
    -- 2.2. instantiate x := s in H2
    have s2_2 : f s = 4 * s + 5 := by exact (hH2 s)
    -- 2.3. algebra, from 2.1, 2.2
    have s2_3 : y = 4 * (s + 1) + 1 := by linear_combination (norm := parley_norm) s2_1 + s2_2
    -- 2.4. exhibit, from 2.3
    have s2_4 : ∃ k : ℤ, y = 4 * k + 1 := ⟨s + 1, s2_3⟩
    -- 2.5. def:set-image u := y, from 2.4
    exact ((Parley.Items.Stdlib.Functions.def_set_image (E := (fun k : ℤ => 4 * k + 1)) (Y := (Set.univ : Set ℤ)) (u := y) (Z := Set.univ) (by parley_whole_side))).mpr (by parley_set_side)
  -- 3. def:subset, from 2
  have s3 : f '' ((Set.univ : Set ℤ) ∩ (Set.univ : Set ℤ)) ⊆ (fun k : ℤ => 4 * k + 1) '' (Set.univ : Set ℤ) := ((Parley.Items.Stdlib.Sets.def_subset (X := f '' ((Set.univ : Set ℤ) ∩ (Set.univ : Set ℤ))) (Y := (fun k : ℤ => 4 * k + 1) '' (Set.univ : Set ℤ)))).mpr s2
  -- 4. proof
  have s4 : ∀ y ∈ (fun k : ℤ => 4 * k + 1) '' (Set.univ : Set ℤ), y ∈ f '' ((Set.univ : Set ℤ) ∩ (Set.univ : Set ℤ)) := by
    intro y hK2
    -- 4.1. obtain m: def:set-image u := y, from K2
    obtain ⟨m, _, s4_1⟩ := ((Parley.Items.Stdlib.Functions.def_set_image (E := (fun k : ℤ => 4 * k + 1)) (Y := (Set.univ : Set ℤ)) (u := y) (Z := Set.univ) (by parley_whole_side))).mp hK2
    -- 4.2. instantiate x := m − 1 in H2
    have s4_2 : f (m - 1) = 4 * (m - 1) + 5 := by exact (hH2 (m - 1))
    -- 4.3. mun:value-in-image Y := ℤ, s := m − 1, from 1
    have s4_3 : f (m - 1) ∈ f '' ((Set.univ : Set ℤ) ∩ (Set.univ : Set ℤ)) := by exact (Parley.Items.Stdlib.Functions.mun_value_in_image (X := (Set.univ : Set ℤ)) (Y := (Set.univ : Set ℤ)) (f := f) (s := m - 1) (W := Set.univ) (by parley_whole_side) (by parley_whole_side) (by parley_whole_side))
    -- 4.4. substitute
    have c1 : f (m - 1) = y := by linear_combination (norm := parley_norm) (-1) * s4_1 + s4_2
    have row1 : y ∈ f '' ((Set.univ : Set ℤ) ∩ (Set.univ : Set ℤ)) := by (have h := Eq.subst (motive := (fun t : ℤ => t ∈ f '' ((Set.univ : Set ℤ) ∩ (Set.univ : Set ℤ)))) c1 s4_3; push_cast at h ⊢; all_goals exact_mod_cast h)
    exact row1
  -- 5. def:subset, from 4
  have s5 : (fun k : ℤ => 4 * k + 1) '' (Set.univ : Set ℤ) ⊆ f '' ((Set.univ : Set ℤ) ∩ (Set.univ : Set ℤ)) := ((Parley.Items.Stdlib.Sets.def_subset (X := (fun k : ℤ => 4 * k + 1) '' (Set.univ : Set ℤ)) (Y := f '' ((Set.univ : Set ℤ) ∩ (Set.univ : Set ℤ))))).mpr s4
  -- 6. mun:subset-antisymmetric, from 3, 5
  exact (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := f '' ((Set.univ : Set ℤ) ∩ (Set.univ : Set ℤ))) (Y := (fun k : ℤ => 4 * k + 1) '' (Set.univ : Set ℤ)) s3 s5)

end Parley.Proofs.Hammack.ImageOfAffineMap.ImageOfAffineMap
