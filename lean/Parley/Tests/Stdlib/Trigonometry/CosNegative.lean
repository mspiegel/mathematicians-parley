module

public import PowerTactics
public import Tactics
public import Parley.Items.Stdlib.Trigonometry

/-! Written from tests/stdlib/trigonometry.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Trigonometry.CosNegative

theorem cos_negative (a : ℂ) :
    Complex.cos (-a) = Complex.cos a := by
  -- 1. mun:trigonometry-cos-negative
  have s1 : Complex.cos (-a) = Complex.cos a := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Trigonometry.mun_cos_negative (a := a)) | (have h := (Parley.Items.Stdlib.Trigonometry.mun_cos_negative (a := a)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Trigonometry.mun_cos_negative (a := a)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Trigonometry.mun_cos_negative (a := a)) | exact_mod_cast ((Parley.Items.Stdlib.Trigonometry.mun_cos_negative (a := a))).symm | (have h := (Parley.Items.Stdlib.Trigonometry.mun_cos_negative (a := a)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Trigonometry.mun_cos_negative (a := a)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Trigonometry.mun_cos_negative (a := a)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Trigonometry.mun_cos_negative (a := a)); parley_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Trigonometry.CosNegative
