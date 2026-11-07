module

public import AlgebraTactics
public import NormTactics
public import PowerTactics
public import SubstTactics
public import Tactics
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Parley.Items.Stdlib.Trigonometry

/-! Written from proofs/setmm/sine-of-double.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.SineOfDouble.SineOfDouble

theorem sine_of_double (A : ℂ) :
    Complex.sin (2 * A) = 2 * Complex.sin A * Complex.cos A := by
  -- 1. algebra
  have s1 : 2 * A = A + A := by parley_ring
  -- 2. calculation
  have s2 : Complex.sin (2 * A) = 2 * Complex.sin A * Complex.cos A := by
    calc Complex.sin (2 * A) = Complex.sin (A + A) := by parley_subst s1
      _ = Complex.sin A * Complex.cos A + Complex.cos A * Complex.sin A := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Trigonometry.thm_sin_add (a := A) (b := A)) | (have h := (Parley.Items.Stdlib.Trigonometry.thm_sin_add (a := A) (b := A)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Trigonometry.thm_sin_add (a := A) (b := A)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Trigonometry.thm_sin_add (a := A) (b := A)) | exact_mod_cast ((Parley.Items.Stdlib.Trigonometry.thm_sin_add (a := A) (b := A))).symm | (have h := (Parley.Items.Stdlib.Trigonometry.thm_sin_add (a := A) (b := A)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Trigonometry.thm_sin_add (a := A) (b := A)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Trigonometry.thm_sin_add (a := A) (b := A)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Trigonometry.thm_sin_add (a := A) (b := A)); parley_side)
      _ = 2 * Complex.sin A * Complex.cos A := by parley_ring
  all_goals exact s2

end Parley.Proofs.Setmm.SineOfDouble.SineOfDouble
