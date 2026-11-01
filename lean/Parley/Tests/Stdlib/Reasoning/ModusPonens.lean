module

public import Parley.Items.Stdlib.Reasoning
public import Parley.Library

/-! Written from tests/stdlib/reasoning.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Reasoning.ModusPonens

theorem modus_ponens (x : ℝ) (hH2 : x = 0 → x ≤ 0) (hH3 : x = 0) :
    x ≤ 0 := by
  -- 1. mun:reasoning-modus-ponens, from H2, H3
  have s1 : x ≤ 0 := by first | linarith [(Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := x = 0) (Q := x ≤ 0) (by parley_side) (by parley_side))] | (have h := (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := x = 0) (Q := x ≤ 0) (by parley_side) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := x = 0) (Q := x ≤ 0) (by parley_side) (by parley_side))
  all_goals parley_side

end Parley.Tests.Stdlib.Reasoning.ModusPonens
