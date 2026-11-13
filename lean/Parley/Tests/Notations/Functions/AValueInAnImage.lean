module

public import SetTactics
public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Function
public import Mathlib.Data.Set.Operations
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.SetNotationForOrder
public import Parley.Items.Stdlib.Functions
public import Parley.Items.Stdlib.Sets

/-! Written from tests/notations/functions.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Functions.AValueInAnImage

theorem a_value_in_an_image (f : ℝ → ℝ) (hH2 : ∀ x : ℝ, f x = 2 * x + 1) :
    (3 : ℝ) ∈ f '' ((Set.univ : Set ℝ) ∩ ({(1 : ℝ), (2 : ℝ)} : Set ℝ)) := by
  -- 1. inspection
  have s1 : (1 : ℤ) ∈ ({(1 : ℤ), (2 : ℤ)} : Set ℤ) := by simp
  -- 2. mun:pair-subset a := 1, b := 2, X := ℝ
  have s2 : ({(1 : ℝ), (2 : ℝ)} : Set ℝ) ⊆ (Set.univ : Set ℝ) := by exact (Parley.Items.Stdlib.Sets.mun_pair_subset (X := (Set.univ : Set ℝ)) (a := (1 : ℝ)) (b := (2 : ℝ)) (Set.mem_univ _) (Set.mem_univ _))
  -- 3. mun:value-in-image, from 1, 2
  have s3 : f 1 ∈ f '' ((Set.univ : Set ℝ) ∩ ({(1 : ℝ), (2 : ℝ)} : Set ℝ)) := by exact (Parley.Items.Stdlib.Functions.mun_value_in_image (X := (Set.univ : Set ℝ)) (Y := ({(1 : ℝ), (2 : ℝ)} : Set ℝ)) (f := f) (s := (1 : ℝ)) (W := Set.univ) s2 (by (have h := s1; revert h; norm_num)) (Set.mapsTo_univ _ _))
  -- 4. instantiate x := 1 in H2
  have s4 : f 1 = 2 * 1 + 1 := by exact (hH2 (1 : ℝ))
  -- 5. calculation
  have s5 : f 1 = 3 := by
    calc f 1 = 2 * 1 + 1 := s4
      _ = 3 := by norm_num
  -- 6. substitute f(1) = 3 (line 5) into line 3
  (have h := Eq.subst (motive := (fun t : ℝ => t ∈ f '' ((Set.univ : Set ℝ) ∩ ({(1 : ℝ), (2 : ℝ)} : Set ℝ)))) s5 s3; push_cast at h ⊢; all_goals exact_mod_cast h)

end Parley.Tests.Notations.Functions.AValueInAnImage
