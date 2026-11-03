module

public import Tactics
public import Parley.Items.Stdlib.Divisibility

/-! Written from proofs/wiedijk/sqrt2-irrational.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.Sqrt2Irrational.OddSquare

theorem odd_square (n : ℤ) (hH2 : Odd n) :
    Odd (n ^ 2) := by
  -- 1. obtain k: def:odd, from H2
  obtain ⟨k, s1⟩ := ((Parley.Items.Stdlib.Divisibility.def_odd (n := n))).mp (by parley_side)
  -- 2. calculation
  have s2 : n ^ 2 = 2 * (2 * k ^ 2 + 2 * k) + 1 := by
    calc n ^ 2 = (2 * k + 1) ^ 2 := by parley_subst s1
      _ = 4 * k ^ 2 + 4 * k + 1 := by parley_ring
      _ = 2 * (2 * k ^ 2 + 2 * k) + 1 := by parley_ring
  -- 3. def:odd n := n², from 2
  have s3 : Odd (n ^ 2) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_odd (n := n ^ 2))).mpr ⟨2 * k ^ 2 + 2 * k, by parley_side⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_odd (n := n ^ 2))).mpr ⟨2 * k ^ 2 + 2 * k, by parley_side⟩; parley_side)
  all_goals exact s3

end Parley.Proofs.Wiedijk.Sqrt2Irrational.OddSquare
