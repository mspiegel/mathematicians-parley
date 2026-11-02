module

public import LeanBridges
public import Parley.Proofs.Wiedijk.DivisibilityByThree.CongruentTimes

/-! Written from tests/elaborator/a-congruence-read-either-way.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ACongruenceReadEitherWay.ACongruenceCitedTheOtherWayRound

theorem a_congruence_cited_the_other_way_round (a : ℤ) (b : ℤ) (c : ℤ) (n : ℕ) (hH4 : 0 < n) (hH5 : b ≡ a [ZMOD (n : ℤ)]) :
    (a * c) ≡ (b * c) [ZMOD (n : ℤ)] := by
  -- 1. thm:congruent-times, from H5
  have s1 : (a * c) ≡ (b * c) [ZMOD (n : ℤ)] := by first | exact (Parley.Proofs.Wiedijk.DivisibilityByThree.CongruentTimes.congruent_times (a := a) (b := b) (c := c) (n := n) (by parley_side) (by parley_side)) | exact ((Parley.Proofs.Wiedijk.DivisibilityByThree.CongruentTimes.congruent_times (a := a) (b := b) (c := c) (n := n) (by parley_side) (by parley_side))).symm | simpa using (Parley.Proofs.Wiedijk.DivisibilityByThree.CongruentTimes.congruent_times (a := a) (b := b) (c := c) (n := n) (by parley_side) (by parley_side)) | exact_mod_cast (Parley.Proofs.Wiedijk.DivisibilityByThree.CongruentTimes.congruent_times (a := a) (b := b) (c := c) (n := n) (by parley_side) (by parley_side))
  all_goals parley_side

end Parley.Tests.Elaborator.ACongruenceReadEitherWay.ACongruenceCitedTheOtherWayRound
