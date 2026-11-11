module

public import Tactics
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.ModEq

/-! Written from tests/elaborator/reading-congruence.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingCongruence.ACongruenceTheOtherWayJoined

theorem a_congruence_the_other_way_joined (a : ℤ) (b : ℤ) (n : ℤ) (hH3 : 0 < n) (hH4 : b ≡ a [ZMOD n]) :
    a ≡ b [ZMOD n] := by
  -- 1. restate H4
  exact hH4.symm

end Parley.Tests.Elaborator.ReadingCongruence.ACongruenceTheOtherWayJoined
