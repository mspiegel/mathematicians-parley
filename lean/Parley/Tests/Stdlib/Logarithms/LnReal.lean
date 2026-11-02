module

public import LeanBridges
public import Parley.Items.Stdlib.Logarithms

/-! Written from tests/stdlib/logarithms.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Logarithms.LnReal

theorem ln_real (x : ℝ) (hH2 : x > 0) :
    True := by
  -- 1. mun:logarithms-ln-real, from H2
  all_goals parley_side

end Parley.Tests.Stdlib.Logarithms.LnReal
