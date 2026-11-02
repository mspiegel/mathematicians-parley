module

public import LeanBridges
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/stdlib/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Numbers.IntegerStep

theorem integer_step (m : ℤ) (n : ℤ) (hH3 : m < n) :
    m + 1 ≤ n := by
  -- 1. mun:numbers-integer-step, from H3
  have s1 : m + 1 ≤ n := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_integer_step (m := m) (n := n) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_integer_step (m := m) (n := n) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_integer_step (m := m) (n := n) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_integer_step (m := m) (n := n) (by parley_side)); parley_side)
  all_goals parley_side

end Parley.Tests.Stdlib.Numbers.IntegerStep
