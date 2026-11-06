module

public import SetTactics
public import Tactics
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Topology.Defs.Filter
public import Parley.Items.Stdlib.Trigonometry

/-! Written from tests/stdlib/trigonometry.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Trigonometry.ContinuousArctan

theorem continuous_arctan (E : Set ℝ) (hH1 : E ⊆ (Set.univ : Set ℝ)) (h : ℝ → ℝ) (hH2 : Set.MapsTo h E (Set.univ : Set ℝ)) (hH3 : ∀ y ∈ E, h y = Real.arctan y) :
    ContinuousOn h E := by
  -- 1. thm:trigonometry-continuous-arctan D := E, g := h, from H1, H3
  have s1 : ContinuousOn h E := by first | exact (Parley.Items.Stdlib.Trigonometry.thm_continuous_arctan (g := h) (D := E) hH1 (by parley_set_side)) | exact ((Parley.Items.Stdlib.Trigonometry.thm_continuous_arctan (g := h) (D := E) hH1 (by parley_set_side))).symm | simpa using (Parley.Items.Stdlib.Trigonometry.thm_continuous_arctan (g := h) (D := E) hH1 (by parley_set_side)) | exact_mod_cast (Parley.Items.Stdlib.Trigonometry.thm_continuous_arctan (g := h) (D := E) hH1 (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Trigonometry.thm_continuous_arctan (g := h) (D := E) hH1 (by parley_set_side)); parley_set_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Trigonometry.ContinuousArctan
