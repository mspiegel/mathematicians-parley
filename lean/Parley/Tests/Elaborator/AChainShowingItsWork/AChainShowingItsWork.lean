module

public import Parley.Items.Stdlib.Divisibility
public import Parley.Library

/-! Written from tests/elaborator/a-chain-showing-its-work.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AChainShowingItsWork.AChainShowingItsWork

theorem a_chain_showing_its_work (n : ℤ) (H2 : Odd n) :
    Odd (n ^ 2) := by
  -- 1. obtain k: def:odd, from H2
  obtain ⟨k, s1⟩ := ((Parley.Items.Stdlib.Divisibility.def_odd (n := n))).mp (by parley_side)
  -- 2. calculation
  have s2 : n ^ 2 = 2 * (2 * k ^ 2 + 2 * k) + 1 := by
    calc n ^ 2 = (2 * k + 1) ^ 2 := by parley_subst s1
      _ = 4 * k ^ 2 + 4 * k + 1 := by ring
      _ = 2 * (2 * k ^ 2 + 2 * k) + 1 := by ring
  -- 3. def:odd n := n², from 2
  have s3 : Odd (n ^ 2) := ((Parley.Items.Stdlib.Divisibility.def_odd (n := n ^ 2))).mpr ⟨2 * k ^ 2 + 2 * k, by parley_side⟩
  all_goals parley_side

end Parley.Tests.Elaborator.AChainShowingItsWork.AChainShowingItsWork
