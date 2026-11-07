module

public import Tactics
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Proofs.Wiedijk.DivisibilityByThree.CongruentTimes

/-! Written from tests/elaborator/a-congruence-read-either-way.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ACongruenceReadEitherWay.ACongruenceCitedTheOtherWayRound

theorem a_congruence_cited_the_other_way_round (a : ℤ) (b : ℤ) (c : ℤ) (n : ℤ) (hH4 : 0 < n) (hH5 : b ≡ a [ZMOD n]) :
    a * c ≡ b * c [ZMOD n] := by
  -- 1. thm:congruent-times, from H5
  have s1 : a * c ≡ b * c [ZMOD n] := by exact (Parley.Proofs.Wiedijk.DivisibilityByThree.CongruentTimes.congruent_times (a := a) (b := b) (c := c) (n := n) (by parley_side) (by parley_side))
  all_goals exact s1

end Parley.Tests.Elaborator.ACongruenceReadEitherWay.ACongruenceCitedTheOtherWayRound
