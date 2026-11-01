module

public import Parley.Items.Stdlib.Divisibility
public import Parley.Library

/-! Written from proofs/hammack/binomial-even-for-odd-k.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.BinomialEvenForOddK.EvenTimes

theorem even_times (A : ℤ) (B : ℤ) (hH3 : Even A) :
    Even (A * B) := by
  -- 1. obtain a: def:even, from H3
  obtain ⟨a, s1⟩ := ((Parley.Items.Stdlib.Divisibility.def_even (n := A))).mp (by parley_side)
  -- 2. algebra, from 1
  have s2 : A * B = 2 * (a * B) := by linear_combination (norm := parley_norm) (B) * s1
  -- 3. def:even n := A·B, from 2
  have s3 : Even (A * B) := ((Parley.Items.Stdlib.Divisibility.def_even (n := A * B))).mpr ⟨a * B, by parley_side⟩
  all_goals parley_side

end Parley.Proofs.Hammack.BinomialEvenForOddK.EvenTimes
