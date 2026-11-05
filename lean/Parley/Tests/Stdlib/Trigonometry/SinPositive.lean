module

public import SetTactics
public import Tactics
public import Parley.Items.Stdlib.Trigonometry

/-! Written from tests/stdlib/trigonometry.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Trigonometry.SinPositive

theorem sin_positive (a : ℝ) (hH1 : a ∈ (Set.Ioo (0 : ℝ) Real.pi : Set ℝ)) :
    0 < Real.sin a := by
  -- 1. mun:trigonometry-sin-positive, from H1
  have s1 : 0 < Real.sin a := by first | linarith [(Parley.Items.Stdlib.Trigonometry.mun_sin_positive (a := a) hH1)] | (have h := (Parley.Items.Stdlib.Trigonometry.mun_sin_positive (a := a) hH1); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Trigonometry.mun_sin_positive (a := a) hH1) | (have h := (Parley.Items.Stdlib.Trigonometry.mun_sin_positive (a := a) hH1); parley_set_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Trigonometry.SinPositive
