module

public import Tactics
public import Mathlib.Algebra.Group.Even
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Divisibility

/-! Written from tests/elaborator/reading-sentences.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingSentences.ASecondSentenceUnfolded

theorem a_second_sentence_unfolded (a : ℝ) (b : ℤ) (hH3a : a = 1) (hH3b : Even b) :
    (∃ k : ℤ, b = 2 * k) := by
  -- 1. def:even n := b, from H3
  have s1 : ∃ k : ℤ, b = 2 * k := by first | exact ((Parley.Items.Stdlib.Divisibility.def_even (n := b))).mp (by parley_side) | exact (((Parley.Items.Stdlib.Divisibility.def_even (n := b))).mp (by parley_side)).symm | simpa using ((Parley.Items.Stdlib.Divisibility.def_even (n := b))).mp (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Divisibility.def_even (n := b))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Divisibility.def_even (n := b))).mp (by parley_side); parley_side)
  all_goals exact s1

end Parley.Tests.Elaborator.ReadingSentences.ASecondSentenceUnfolded
