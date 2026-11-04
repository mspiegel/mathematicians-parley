module

public import ComplexTactics
public import PowerTactics
public import Tactics
public import Parley.Items.Stdlib.Trigonometry

/-! Written from tests/stdlib/trigonometry.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Trigonometry.SinCosSquares

theorem sin_cos_squares (a : ℂ) :
    Complex.sin a ^ 2 + Complex.cos a ^ 2 = 1 := by
  -- 1. mun:trigonometry-sin-cos-squares
  have s1 : Complex.sin a ^ 2 + Complex.cos a ^ 2 = 1 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Trigonometry.mun_sin_cos_squares (a := a)) | (have h := (Parley.Items.Stdlib.Trigonometry.mun_sin_cos_squares (a := a)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Trigonometry.mun_sin_cos_squares (a := a)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Trigonometry.mun_sin_cos_squares (a := a)) | exact_mod_cast ((Parley.Items.Stdlib.Trigonometry.mun_sin_cos_squares (a := a))).symm | (have h := (Parley.Items.Stdlib.Trigonometry.mun_sin_cos_squares (a := a)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Trigonometry.mun_sin_cos_squares (a := a)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Trigonometry.mun_sin_cos_squares (a := a)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Trigonometry.mun_sin_cos_squares (a := a)); parley_of_complex h) | (have h := (Parley.Items.Stdlib.Trigonometry.mun_sin_cos_squares (a := a)); parley_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Trigonometry.SinCosSquares
