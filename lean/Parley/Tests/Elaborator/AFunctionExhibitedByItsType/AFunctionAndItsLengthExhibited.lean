module

public import SetTactics
public import Tactics
public import WholeTactics
public import Parley.Items.Stdlib.Functions

/-! Written from tests/elaborator/a-function-exhibited-by-its-type.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AFunctionExhibitedByItsType.AFunctionAndItsLengthExhibited

theorem a_function_and_its_length_exhibited (n : ℕ) (hH1 : 0 < n) :
    (∃ k : ℕ, 0 < k ∧ (∃ f : ℤ → ℤ, Set.MapsTo f (Set.Icc (1 : ℤ) (k : ℤ) : Set ℤ) {n : ℤ | 0 < n} ∧ (∀ i : ℤ, i ∈ Finset.Icc 1 (k : ℤ) → f i = 1))) := by
  set g : ℤ → ℤ := fun i => (1 : ℤ) with hD1
  -- 1. D1
  have s1 : ∀ i : ℤ, i ∈ Finset.Icc 1 (n : ℤ) → g i = 1 := by parley_set_side
  -- 2. membership, from D1
  have s2 : ∀ i : ℤ, i ∈ Finset.Icc 1 (n : ℤ) → 0 < g i := by intro i h_i; parley_set_side
  -- 3. mun:function-into, from 2
  have s3 : Set.MapsTo g (Set.Icc (1 : ℤ) (n : ℤ) : Set ℤ) {n : ℤ | 0 < n} := by first | exact (Parley.Items.Stdlib.Functions.mun_function_into (E := g) (X := (Set.Icc (1 : ℤ) (n : ℤ) : Set ℤ)) (Y := {n : ℤ | 0 < n}) (by parley_set_side) (by parley_whole_side)) | exact ((Parley.Items.Stdlib.Functions.mun_function_into (E := g) (X := (Set.Icc (1 : ℤ) (n : ℤ) : Set ℤ)) (Y := {n : ℤ | 0 < n}) (by parley_set_side) (by parley_whole_side))).symm | simpa using (Parley.Items.Stdlib.Functions.mun_function_into (E := g) (X := (Set.Icc (1 : ℤ) (n : ℤ) : Set ℤ)) (Y := {n : ℤ | 0 < n}) (by parley_set_side) (by parley_whole_side)) | exact_mod_cast (Parley.Items.Stdlib.Functions.mun_function_into (E := g) (X := (Set.Icc (1 : ℤ) (n : ℤ) : Set ℤ)) (Y := {n : ℤ | 0 < n}) (by parley_set_side) (by parley_whole_side)) | (have h := (Parley.Items.Stdlib.Functions.mun_function_into (E := g) (X := (Set.Icc (1 : ℤ) (n : ℤ) : Set ℤ)) (Y := {n : ℤ | 0 < n}) (by parley_set_side) (by parley_whole_side)); parley_set_side)
  -- 4. exhibit, from 1, 3
  have s4 : ∃ k : ℕ, 0 < k ∧ (∃ f : ℤ → ℤ, Set.MapsTo f (Set.Icc (1 : ℤ) (k : ℤ) : Set ℤ) {n : ℤ | 0 < n} ∧ (∀ i : ℤ, i ∈ Finset.Icc 1 (k : ℤ) → f i = 1)) := ⟨n, by parley_set_side, g, by parley_set_side, by parley_set_side⟩
  all_goals exact s4

end Parley.Tests.Elaborator.AFunctionExhibitedByItsType.AFunctionAndItsLengthExhibited
