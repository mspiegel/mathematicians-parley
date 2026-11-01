module

public import Parley.Items.Stdlib.Divisibility
public import Parley.Library

/-! Written from proofs/hammack/divides-cubic.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.DividesCubic.DividesCubic

theorem divides_cubic (a : ℤ) (b : ℤ) (hH3 : a ∣ b) :
    a ∣ 3 * b ^ 3 - b ^ 2 + 5 * b := by
  -- 1. obtain k: def:divides, from H3
  obtain ⟨k, s1⟩ := ((Parley.Items.Stdlib.Divisibility.def_divides (d := a) (n := b))).mp (by parley_side)
  -- 2. calculation
  have s2 : 3 * b ^ 3 - b ^ 2 + 5 * b = a * (3 * a ^ 2 * k ^ 3 - a * k ^ 2 + 5 * k) := by
    calc 3 * b ^ 3 - b ^ 2 + 5 * b = 3 * (a * k) ^ 3 - (a * k) ^ 2 + 5 * (a * k) := by parley_subst s1
      _ = a * (3 * a ^ 2 * k ^ 3 - a * k ^ 2 + 5 * k) := by ring
  -- 3. def:divides d := a, n := 3b³ − b² + 5b, from 2
  have s3 : a ∣ 3 * b ^ 3 - b ^ 2 + 5 * b := ((Parley.Items.Stdlib.Divisibility.def_divides (d := a) (n := 3 * b ^ 3 - b ^ 2 + 5 * b))).mpr ⟨3 * a ^ 2 * k ^ 3 - a * k ^ 2 + 5 * k, by parley_side⟩
  all_goals parley_side

end Parley.Proofs.Hammack.DividesCubic.DividesCubic
