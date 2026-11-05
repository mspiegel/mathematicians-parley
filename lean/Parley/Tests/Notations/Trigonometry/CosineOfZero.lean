module

public import PowerTactics
public import Tactics
public import Parley.Items.Stdlib.Trigonometry

/-! Written from tests/notations/trigonometry.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Trigonometry.CosineOfZero

theorem cosine_of_zero :
    Real.cos (0 : ℝ) = 1 := by
  -- 1. mun:cos-zero
  have s1 : Real.cos (0 : ℝ) = 1 := by first | linear_combination (norm := parley_norm) Parley.Items.Stdlib.Trigonometry.mun_cos_zero | (have h := Parley.Items.Stdlib.Trigonometry.mun_cos_zero; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := Parley.Items.Stdlib.Trigonometry.mun_cos_zero; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast Parley.Items.Stdlib.Trigonometry.mun_cos_zero | exact_mod_cast (Parley.Items.Stdlib.Trigonometry.mun_cos_zero).symm | (have h := Parley.Items.Stdlib.Trigonometry.mun_cos_zero; rify; linear_combination (norm := parley_norm) h) | (have h := Parley.Items.Stdlib.Trigonometry.mun_cos_zero; qify; linear_combination (norm := parley_norm) h) | (have h := Parley.Items.Stdlib.Trigonometry.mun_cos_zero; parley_int_power h) | (have h := Parley.Items.Stdlib.Trigonometry.mun_cos_zero; parley_side)
  all_goals exact s1

end Parley.Tests.Notations.Trigonometry.CosineOfZero
