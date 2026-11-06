module

public import Tactics
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/docs/grammar.proof by parley build lean. -/

public section

namespace Parley.Tests.Docs.Grammar.APowerPlusOne

theorem a_power_plus_one (a : ℤ) (k : ℤ) (hH2 : 0 ≤ k) :
    True := by
  -- 1. mun:int-closure a := a^k, b := 1
  all_goals parley_side

end Parley.Tests.Docs.Grammar.APowerPlusOne
