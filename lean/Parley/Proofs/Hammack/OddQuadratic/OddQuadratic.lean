module

public import Parley.Items.Stdlib.Divisibility
public import Parley.Library

/-! Written from proofs/hammack/odd-quadratic.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.OddQuadratic.OddQuadratic

theorem odd_quadratic (a : ℤ) (H2 : Odd a) :
    Odd (a ^ 2 + 3 * a + 5) := by
  -- 1. obtain k: def:odd, from H2
  obtain ⟨k, s1⟩ := ((Parley.Items.Stdlib.Divisibility.def_odd (n := a))).mp (by parley_side)
  -- 2. calculation
  have s2 : a ^ 2 + 3 * a + 5 = 2 * (2 * k ^ 2 + 5 * k + 4) + 1 := by
    calc a ^ 2 + 3 * a + 5 = (2 * k + 1) ^ 2 + 3 * (2 * k + 1) + 5 := by parley_subst s1
      _ = 2 * (2 * k ^ 2 + 5 * k + 4) + 1 := by ring
  -- 3. def:odd n := a² + 3a + 5, from 2
  have s3 : Odd (a ^ 2 + 3 * a + 5) := ((Parley.Items.Stdlib.Divisibility.def_odd (n := a ^ 2 + 3 * a + 5))).mpr ⟨2 * k ^ 2 + 5 * k + 4, by parley_side⟩
  parley_side

end Parley.Proofs.Hammack.OddQuadratic.OddQuadratic
