module

public import ArithTactics
public import PowerTactics
public import Tactics
public import Parley.Items.Stdlib.Trigonometry

/-! Written from tests/notations/trigonometry.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Trigonometry.CosineOfZeroNotZero

theorem cosine_of_zero_not_zero :
    Real.cos (0 : ℝ) ≠ 0 := by
  -- 1. mun:cos-zero
  have s1 : Real.cos (0 : ℝ) = 1 := by first | linear_combination (norm := parley_norm) Parley.Items.Stdlib.Trigonometry.mun_cos_zero | (have h := Parley.Items.Stdlib.Trigonometry.mun_cos_zero; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := Parley.Items.Stdlib.Trigonometry.mun_cos_zero; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast Parley.Items.Stdlib.Trigonometry.mun_cos_zero | exact_mod_cast (Parley.Items.Stdlib.Trigonometry.mun_cos_zero).symm | (have h := Parley.Items.Stdlib.Trigonometry.mun_cos_zero; rify; linear_combination (norm := parley_norm) h) | (have h := Parley.Items.Stdlib.Trigonometry.mun_cos_zero; qify; linear_combination (norm := parley_norm) h) | (have h := Parley.Items.Stdlib.Trigonometry.mun_cos_zero; parley_int_power h) | (have h := Parley.Items.Stdlib.Trigonometry.mun_cos_zero; parley_side)
  -- 2. contradiction
  have s2 : Real.cos (0 : ℝ) ≠ 0 := by
    by_contra hc_hS
    have hS : Real.cos (0 : ℝ) = 0 := by parley_suppose hc_hS
    -- 2.1. calculation
    have s2_1 : (1 : ℝ) = 0 := by
      try rify
      calc (1 : ℝ) = Real.cos (0 : ℝ) := by parley_side
        _ = 0 := by parley_side
    exact absurd s2_1 (by norm_num)
    all_goals parley_side
  all_goals exact s2

end Parley.Tests.Notations.Trigonometry.CosineOfZeroNotZero
