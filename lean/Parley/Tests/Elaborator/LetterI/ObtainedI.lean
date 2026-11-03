module

public import Tactics
public import Parley.Items.Stdlib.Divisibility

/-! Written from tests/elaborator/letter-i.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.LetterI.ObtainedI

theorem obtained_i (n : ℤ) (hH2 : Odd n) :
    Odd (n ^ 2) := by
  -- 1. obtain i: def:odd, from H2
  obtain ⟨i, s1⟩ := ((Parley.Items.Stdlib.Divisibility.def_odd (n := n))).mp (by parley_side)
  -- 2. substitute n = 2i + 1 (line 1)
  have s2 : n ^ 2 = (2 * i + 1) ^ 2 := by parley_subst s1
  -- 3. algebra
  have s3 : (2 * i + 1) ^ 2 = 2 * (2 * i ^ 2 + 2 * i) + 1 := by parley_ring
  -- 4. calculation
  have s4 : n ^ 2 = 2 * (2 * i ^ 2 + 2 * i) + 1 := by
    calc n ^ 2 = (2 * i + 1) ^ 2 := by parley_side
      _ = 2 * (2 * i ^ 2 + 2 * i) + 1 := by parley_side
  -- 5. def:odd n := n², from 4
  have s5 : Odd (n ^ 2) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_odd (n := n ^ 2))).mpr ⟨2 * i ^ 2 + 2 * i, by parley_side⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_odd (n := n ^ 2))).mpr ⟨2 * i ^ 2 + 2 * i, by parley_side⟩; parley_side)
  all_goals exact s5

end Parley.Tests.Elaborator.LetterI.ObtainedI
