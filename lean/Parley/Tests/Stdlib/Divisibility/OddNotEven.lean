module

public import Tactics
public import Mathlib.Algebra.Group.Even
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Parity
public import Parley.Items.Stdlib.Divisibility

/-! Written from tests/stdlib/divisibility.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Divisibility.OddNotEven

theorem odd_not_even (n : ℤ) (hH2 : Odd n) :
    ¬ Even n := by
  -- 1. mun:divisibility-odd-not-even, from H2
  have s1 : ¬ Even n := by exact (Parley.Items.Stdlib.Divisibility.mun_odd_not_even (n := n) hH2)
  all_goals exact s1

end Parley.Tests.Stdlib.Divisibility.OddNotEven
