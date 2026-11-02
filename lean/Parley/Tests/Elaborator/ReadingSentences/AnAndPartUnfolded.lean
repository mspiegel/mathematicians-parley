module

public import Parley.Items.Stdlib.Divisibility
public import Parley.Library

/-! Written from tests/elaborator/reading-sentences.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingSentences.AnAndPartUnfolded

theorem an_and_part_unfolded (a : ℝ) (b : ℤ) (hH3 : a = 1 ∧ Even b) :
    (∃ k : ℤ, b = 2 * k) := by
  -- 1. def:even n := b, from H3
  have s1 : ∃ k : ℤ, b = 2 * k := by first | exact ((Parley.Items.Stdlib.Divisibility.def_even (n := b))).mp (by parley_side) | exact (((Parley.Items.Stdlib.Divisibility.def_even (n := b))).mp (by parley_side)).symm | simpa using ((Parley.Items.Stdlib.Divisibility.def_even (n := b))).mp (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Divisibility.def_even (n := b))).mp (by parley_side)
  all_goals parley_side

end Parley.Tests.Elaborator.ReadingSentences.AnAndPartUnfolded
