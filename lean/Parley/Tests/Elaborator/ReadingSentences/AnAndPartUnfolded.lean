module

public import Mathlib.Algebra.Group.Even
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Divisibility

/-! Written from tests/elaborator/reading-sentences.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingSentences.AnAndPartUnfolded

theorem an_and_part_unfolded (a : ℝ) (b : ℤ) (hH3 : a = 1 ∧ Even b) :
    (∃ k : ℤ, b = 2 * k) := by
  -- 1. def:even n := b, from H3
  exact ((Parley.Items.Stdlib.Divisibility.def_even (n := b))).mp hH3.2

end Parley.Tests.Elaborator.ReadingSentences.AnAndPartUnfolded
