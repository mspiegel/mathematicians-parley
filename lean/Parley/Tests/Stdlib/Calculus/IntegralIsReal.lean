module

public import SetTactics
public import Tactics
public import Parley.Items.Stdlib.Calculus

/-! Written from tests/stdlib/calculus.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Calculus.IntegralIsReal

theorem integral_is_real (c : ℝ) (d : ℝ) (hH3 : c < d) (g : ℝ → ℝ) (hH4 : Set.MapsTo g (Set.Icc c d : Set ℝ) (Set.univ : Set ℝ)) (hH5 : ContinuousOn g (Set.Icc c d : Set ℝ)) (y : ℝ) (hH6 : y ∈ (Set.Icc c d : Set ℝ)) :
    True := by
  -- 1. mun:integral-real a := c, b := d, f := g, x := y, from H3, H5, H6
  all_goals parley_set_side

end Parley.Tests.Stdlib.Calculus.IntegralIsReal
