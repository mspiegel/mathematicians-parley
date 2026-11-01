module

public import Parley.Items.Stdlib.Divisibility
public import Parley.Library

/-! Written from proofs/hammack/rational-cube-root-of-two.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.RationalCubeRootOfTwo.OddCube

theorem odd_cube (n : ℤ) (H2 : Odd n) :
    Odd (n ^ 3) := by
  -- 1. obtain k: def:odd, from H2
  obtain ⟨k, s1⟩ := ((Parley.Items.Stdlib.Divisibility.def_odd (n := n))).mp (by parley_side)
  -- 2. substitute n = 2k + 1 (line 1)
  have s2 : n ^ 3 = (2 * k + 1) ^ 3 := by parley_subst s1
  -- 3. algebra
  have s3 : (2 * k + 1) ^ 3 = 2 * (4 * k ^ 3 + 6 * k ^ 2 + 3 * k) + 1 := by ring
  -- 4. transitivity, from 2, 3
  have s4 : n ^ 3 = 2 * (4 * k ^ 3 + 6 * k ^ 2 + 3 * k) + 1 := by parley_side
  -- 5. def:odd n := n³, from 4
  have s5 : Odd (n ^ 3) := ((Parley.Items.Stdlib.Divisibility.def_odd (n := n ^ 3))).mpr ⟨4 * k ^ 3 + 6 * k ^ 2 + 3 * k, by parley_side⟩
  parley_side

end Parley.Proofs.Hammack.RationalCubeRootOfTwo.OddCube
