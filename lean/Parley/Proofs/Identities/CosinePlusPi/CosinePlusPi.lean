module

public import AlgebraTactics
public import ComplexTactics
public import NormTactics
public import PowerTactics
public import RealTactics
public import Tactics
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Parley.Items.Stdlib.Trigonometry

/-! Written from proofs/identities/cosine-plus-pi.proof by parley build lean. -/

public section

namespace Parley.Proofs.Identities.CosinePlusPi.CosinePlusPi

theorem cosine_plus_pi (x : ℝ) :
    Real.cos (x + Real.pi) = -Real.cos x := by
  -- 1. calculation
  have s1 : Real.cos (x + Real.pi) = -Real.cos x := by
    calc Real.cos (x + Real.pi) = Real.cos x * Real.cos Real.pi - Real.sin x * Real.sin Real.pi := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Trigonometry.thm_cos_add (a := (x : ℂ)) (b := (Real.pi : ℂ))) | (have h := (Parley.Items.Stdlib.Trigonometry.thm_cos_add (a := (x : ℂ)) (b := (Real.pi : ℂ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Trigonometry.thm_cos_add (a := (x : ℂ)) (b := (Real.pi : ℂ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Trigonometry.thm_cos_add (a := (x : ℂ)) (b := (Real.pi : ℂ))) | exact_mod_cast ((Parley.Items.Stdlib.Trigonometry.thm_cos_add (a := (x : ℂ)) (b := (Real.pi : ℂ)))).symm | (have h := (Parley.Items.Stdlib.Trigonometry.thm_cos_add (a := (x : ℂ)) (b := (Real.pi : ℂ))); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Trigonometry.thm_cos_add (a := (x : ℂ)) (b := (Real.pi : ℂ))); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Trigonometry.thm_cos_add (a := (x : ℂ)) (b := (Real.pi : ℂ))); parley_int_power h) | (have h := (Parley.Items.Stdlib.Trigonometry.thm_cos_add (a := (x : ℂ)) (b := (Real.pi : ℂ))); parley_of_complex h) | (have h := (Parley.Items.Stdlib.Trigonometry.thm_cos_add (a := (x : ℂ)) (b := (Real.pi : ℂ))); parley_side)
      _ = Real.cos x * -1 - Real.sin x * Real.sin Real.pi := by parley_real
      _ = Real.cos x * -1 - Real.sin x * 0 := by parley_real
      _ = -Real.cos x := by parley_ring
  all_goals exact s1

end Parley.Proofs.Identities.CosinePlusPi.CosinePlusPi
