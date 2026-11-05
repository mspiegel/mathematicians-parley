module

public import SetTactics
public import Tactics
public import Parley.Items.Stdlib.Trigonometry

/-! Written from tests/stdlib/trigonometry.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Trigonometry.CosNonneg

theorem cos_nonneg (a : ℝ) (hH1 : a ∈ (Set.Icc (-(Real.pi / 2)) (Real.pi / 2) : Set ℝ)) :
    0 ≤ Real.cos a := by
  -- 1. mun:trigonometry-cos-nonneg, from H1
  have s1 : 0 ≤ Real.cos a := by first | linarith [(Parley.Items.Stdlib.Trigonometry.mun_cos_nonneg (a := a) hH1)] | (have h := (Parley.Items.Stdlib.Trigonometry.mun_cos_nonneg (a := a) hH1); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Trigonometry.mun_cos_nonneg (a := a) hH1) | (have h := (Parley.Items.Stdlib.Trigonometry.mun_cos_nonneg (a := a) hH1); parley_set_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Trigonometry.CosNonneg
