module

public import Functions
public import PowerTactics
public import RealTactics
public import SetTactics
public import SubstTactics
public import Tactics
public import WholeTactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Parley.Items.Stdlib.Functions

/-! Written from tests/notations/functions.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Functions.AnInverseValue

theorem an_inverse_value (f : ℝ → ℝ) (hH1 : Set.MapsTo f (Set.univ : Set ℝ) (Set.univ : Set ℝ) ∧ Set.InjOn f (Set.univ : Set ℝ)) (hH2 : ∀ x : ℝ, f x = 2 * x + 1) :
    (LeanBridges.Functions.inverse f (Set.univ : Set ℝ)) 7 = 3 := by
  -- 1. mun:inverse-value, from H1
  have s1 : (LeanBridges.Functions.inverse f (Set.univ : Set ℝ)) (f 3) = 3 := by first | exact (Parley.Items.Stdlib.Functions.mun_inverse_value (X := (Set.univ : Set ℝ)) (Y := (Set.univ : Set ℝ)) (g := f) (y := (3 : ℝ)) (by parley_whole_side) (by parley_whole_side)) | exact ((Parley.Items.Stdlib.Functions.mun_inverse_value (X := (Set.univ : Set ℝ)) (Y := (Set.univ : Set ℝ)) (g := f) (y := (3 : ℝ)) (by parley_whole_side) (by parley_whole_side))).symm | simpa using (Parley.Items.Stdlib.Functions.mun_inverse_value (X := (Set.univ : Set ℝ)) (Y := (Set.univ : Set ℝ)) (g := f) (y := (3 : ℝ)) (by parley_whole_side) (by parley_whole_side)) | exact_mod_cast (Parley.Items.Stdlib.Functions.mun_inverse_value (X := (Set.univ : Set ℝ)) (Y := (Set.univ : Set ℝ)) (g := f) (y := (3 : ℝ)) (by parley_whole_side) (by parley_whole_side)) | (have h := (Parley.Items.Stdlib.Functions.mun_inverse_value (X := (Set.univ : Set ℝ)) (Y := (Set.univ : Set ℝ)) (g := f) (y := (3 : ℝ)) (by parley_whole_side) (by parley_whole_side)); parley_rat_of_real h) | (have h := (Parley.Items.Stdlib.Functions.mun_inverse_value (X := (Set.univ : Set ℝ)) (Y := (Set.univ : Set ℝ)) (g := f) (y := (3 : ℝ)) (by parley_whole_side) (by parley_whole_side)); parley_set_side)
  -- 2. instantiate x := 3 in H2
  have s2 : f 3 = 2 * 3 + 1 := by first | linear_combination (norm := parley_norm) (hH2 (3 : ℝ)) | (have h := (hH2 (3 : ℝ)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (hH2 (3 : ℝ)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (hH2 (3 : ℝ)) | exact_mod_cast ((hH2 (3 : ℝ))).symm | (have h := (hH2 (3 : ℝ)); rify; linear_combination (norm := parley_norm) h) | (have h := (hH2 (3 : ℝ)); qify; linear_combination (norm := parley_norm) h) | (have h := (hH2 (3 : ℝ)); parley_int_power h) | (have h := (hH2 (3 : ℝ)); parley_rat_of_real h) | (have h := (hH2 (3 : ℝ)); parley_set_side)
  -- 3. calculation
  have s3 : f 3 = 7 := by
    calc f 3 = 2 * 3 + 1 := by parley_set_side
      _ = 7 := by norm_num
  -- 4. substitute f(3) = 7 (line 3) into line 1
  have s4 : (LeanBridges.Functions.inverse f (Set.univ : Set ℝ)) 7 = 3 := by parley_subst_at s3 s1
  all_goals exact s4

end Parley.Tests.Notations.Functions.AnInverseValue
