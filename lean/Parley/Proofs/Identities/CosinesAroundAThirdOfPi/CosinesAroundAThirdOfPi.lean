module

public import AlgebraTactics
public import ComplexTactics
public import PowerTactics
public import RealTactics
public import SubstTactics
public import Tactics
public import Parley.Items.Stdlib.Trigonometry

/-! Written from proofs/identities/cosines-around-a-third-of-pi.proof by parley build lean. -/

public section

namespace Parley.Proofs.Identities.CosinesAroundAThirdOfPi.CosinesAroundAThirdOfPi

theorem cosines_around_a_third_of_pi (x : ℝ) :
    Real.cos (Real.pi / 3 + x) + Real.cos (Real.pi / 3 - x) = Real.cos x := by
  -- 1. thm:cos-add a := π/3, b := x
  have s1 : Real.cos (Real.pi / 3 + x) = Real.cos (Real.pi / 3) * Real.cos x - Real.sin (Real.pi / 3) * Real.sin x := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Trigonometry.thm_cos_add (a := (Real.pi : ℂ) / 3) (b := (x : ℂ))) | (have h := (Parley.Items.Stdlib.Trigonometry.thm_cos_add (a := (Real.pi : ℂ) / 3) (b := (x : ℂ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Trigonometry.thm_cos_add (a := (Real.pi : ℂ) / 3) (b := (x : ℂ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Trigonometry.thm_cos_add (a := (Real.pi : ℂ) / 3) (b := (x : ℂ))) | exact_mod_cast ((Parley.Items.Stdlib.Trigonometry.thm_cos_add (a := (Real.pi : ℂ) / 3) (b := (x : ℂ)))).symm | (have h := (Parley.Items.Stdlib.Trigonometry.thm_cos_add (a := (Real.pi : ℂ) / 3) (b := (x : ℂ))); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Trigonometry.thm_cos_add (a := (Real.pi : ℂ) / 3) (b := (x : ℂ))); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Trigonometry.thm_cos_add (a := (Real.pi : ℂ) / 3) (b := (x : ℂ))); parley_int_power h) | (have h := (Parley.Items.Stdlib.Trigonometry.thm_cos_add (a := (Real.pi : ℂ) / 3) (b := (x : ℂ))); parley_of_complex h) | (have h := (Parley.Items.Stdlib.Trigonometry.thm_cos_add (a := (Real.pi : ℂ) / 3) (b := (x : ℂ))); parley_side)
  -- 2. thm:cos-add a := π/3, b := −x
  have s2 : Real.cos (Real.pi / 3 + -x) = Real.cos (Real.pi / 3) * Real.cos (-x) - Real.sin (Real.pi / 3) * Real.sin (-x) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Trigonometry.thm_cos_add (a := (Real.pi : ℂ) / 3) (b := -(x : ℂ))) | (have h := (Parley.Items.Stdlib.Trigonometry.thm_cos_add (a := (Real.pi : ℂ) / 3) (b := -(x : ℂ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Trigonometry.thm_cos_add (a := (Real.pi : ℂ) / 3) (b := -(x : ℂ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Trigonometry.thm_cos_add (a := (Real.pi : ℂ) / 3) (b := -(x : ℂ))) | exact_mod_cast ((Parley.Items.Stdlib.Trigonometry.thm_cos_add (a := (Real.pi : ℂ) / 3) (b := -(x : ℂ)))).symm | (have h := (Parley.Items.Stdlib.Trigonometry.thm_cos_add (a := (Real.pi : ℂ) / 3) (b := -(x : ℂ))); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Trigonometry.thm_cos_add (a := (Real.pi : ℂ) / 3) (b := -(x : ℂ))); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Trigonometry.thm_cos_add (a := (Real.pi : ℂ) / 3) (b := -(x : ℂ))); parley_int_power h) | (have h := (Parley.Items.Stdlib.Trigonometry.thm_cos_add (a := (Real.pi : ℂ) / 3) (b := -(x : ℂ))); parley_of_complex h) | (have h := (Parley.Items.Stdlib.Trigonometry.thm_cos_add (a := (Real.pi : ℂ) / 3) (b := -(x : ℂ))); parley_side)
  -- 3. algebra
  have s3 : Real.pi / 3 - x = Real.pi / 3 + -x := by parley_ring
  -- 4. mun:cos-negative a := x
  have s4 : Real.cos (-x) = Real.cos x := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Trigonometry.mun_cos_negative (a := (x : ℂ))) | (have h := (Parley.Items.Stdlib.Trigonometry.mun_cos_negative (a := (x : ℂ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Trigonometry.mun_cos_negative (a := (x : ℂ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Trigonometry.mun_cos_negative (a := (x : ℂ))) | exact_mod_cast ((Parley.Items.Stdlib.Trigonometry.mun_cos_negative (a := (x : ℂ)))).symm | (have h := (Parley.Items.Stdlib.Trigonometry.mun_cos_negative (a := (x : ℂ))); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Trigonometry.mun_cos_negative (a := (x : ℂ))); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Trigonometry.mun_cos_negative (a := (x : ℂ))); parley_int_power h) | (have h := (Parley.Items.Stdlib.Trigonometry.mun_cos_negative (a := (x : ℂ))); parley_of_complex h) | (have h := (Parley.Items.Stdlib.Trigonometry.mun_cos_negative (a := (x : ℂ))); parley_side)
  -- 5. mun:sin-negative a := x
  have s5 : Real.sin (-x) = -Real.sin x := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Trigonometry.mun_sin_negative (a := (x : ℂ))) | (have h := (Parley.Items.Stdlib.Trigonometry.mun_sin_negative (a := (x : ℂ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Trigonometry.mun_sin_negative (a := (x : ℂ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Trigonometry.mun_sin_negative (a := (x : ℂ))) | exact_mod_cast ((Parley.Items.Stdlib.Trigonometry.mun_sin_negative (a := (x : ℂ)))).symm | (have h := (Parley.Items.Stdlib.Trigonometry.mun_sin_negative (a := (x : ℂ))); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Trigonometry.mun_sin_negative (a := (x : ℂ))); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Trigonometry.mun_sin_negative (a := (x : ℂ))); parley_int_power h) | (have h := (Parley.Items.Stdlib.Trigonometry.mun_sin_negative (a := (x : ℂ))); parley_of_complex h) | (have h := (Parley.Items.Stdlib.Trigonometry.mun_sin_negative (a := (x : ℂ))); parley_side)
  -- 6. calculation
  have s6 : Real.cos (Real.pi / 3 + x) + Real.cos (Real.pi / 3 - x) = Real.cos x := by
    calc Real.cos (Real.pi / 3 + x) + Real.cos (Real.pi / 3 - x) = Real.cos (Real.pi / 3 + x) + Real.cos (Real.pi / 3 + -x) := by parley_subst s3
      _ = Real.cos (Real.pi / 3) * Real.cos x - Real.sin (Real.pi / 3) * Real.sin x + Real.cos (Real.pi / 3 + -x) := by parley_subst s1
      _ = Real.cos (Real.pi / 3) * Real.cos x - Real.sin (Real.pi / 3) * Real.sin x + (Real.cos (Real.pi / 3) * Real.cos (-x) - Real.sin (Real.pi / 3) * Real.sin (-x)) := by parley_subst s2
      _ = Real.cos (Real.pi / 3) * Real.cos x - Real.sin (Real.pi / 3) * Real.sin x + (Real.cos (Real.pi / 3) * Real.cos x - Real.sin (Real.pi / 3) * Real.sin (-x)) := by parley_subst s4
      _ = Real.cos (Real.pi / 3) * Real.cos x - Real.sin (Real.pi / 3) * Real.sin x + (Real.cos (Real.pi / 3) * Real.cos x - Real.sin (Real.pi / 3) * -Real.sin x) := by parley_subst s5
      _ = 2 * Real.cos (Real.pi / 3) * Real.cos x := by parley_ring
      _ = 2 * (1 / 2) * Real.cos x := by parley_real
      _ = Real.cos x := by parley_ring
  all_goals exact s6

end Parley.Proofs.Identities.CosinesAroundAThirdOfPi.CosinesAroundAThirdOfPi
