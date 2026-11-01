module

public import Parley.Items.Stdlib.Divisibility
public import Parley.Library

/-! Written from proofs/hammack/binomial-even-for-odd-k.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.BinomialEvenForOddK.OddFactor

theorem odd_factor (A : ℤ) (B : ℤ) (hH3 : Odd A) (hH4 : Even (A * B)) :
    Even B := by
  -- 1. obtain b: def:odd, from H3
  obtain ⟨b, s1⟩ := ((Parley.Items.Stdlib.Divisibility.def_odd (n := A))).mp (by parley_side)
  -- 2. obtain a: def:even n := A·B, from H4
  obtain ⟨a, s2⟩ := ((Parley.Items.Stdlib.Divisibility.def_even (n := A * B))).mp (by parley_side)
  -- 3. substitute A = 2b + 1 (line 1) into line 2
  have s3 : (2 * b + 1) * B = 2 * a := by parley_subst_at s1 s2
  -- 4. algebra, from 3
  have s4 : B = 2 * (a - b * B) := by linear_combination (norm := parley_norm) s3
  -- 5. def:even n := B, from 4
  have s5 : Even B := ((Parley.Items.Stdlib.Divisibility.def_even (n := B))).mpr ⟨a - b * B, by parley_side⟩
  all_goals parley_side

end Parley.Proofs.Hammack.BinomialEvenForOddK.OddFactor
