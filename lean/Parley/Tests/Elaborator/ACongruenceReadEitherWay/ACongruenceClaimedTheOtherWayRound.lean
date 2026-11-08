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

namespace Parley.Tests.Elaborator.ACongruenceReadEitherWay.ACongruenceClaimedTheOtherWayRound

theorem a_congruence_claimed_the_other_way_round (a : ℤ) (b : ℤ) (c : ℤ) (n : ℤ) (hH4 : 0 < n) (hH5 : a ≡ b [ZMOD n]) :
    b * c ≡ a * c [ZMOD n] := by
  -- 1. thm:congruent-times, from H5
  exact (Parley.Proofs.Wiedijk.DivisibilityByThree.CongruentTimes.congruent_times (a := b) (b := a) (c := c) (n := n) (by parley_side) hH5.symm)

end Parley.Tests.Elaborator.ACongruenceReadEitherWay.ACongruenceClaimedTheOtherWayRound
