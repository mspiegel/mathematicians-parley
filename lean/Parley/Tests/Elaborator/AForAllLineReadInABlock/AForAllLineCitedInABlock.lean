module

public import Tactics
public import Parley.Proofs.Wiedijk.DivisibilityByThree.CongruentTimes

/-! Written from tests/elaborator/a-for-all-line-read-in-a-block.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AForAllLineReadInABlock.AForAllLineCitedInABlock

theorem a_for_all_line_cited_in_a_block (n : ℕ) (hH1 : 0 < n) (hH2 : ∀ x : ℤ, x ≡ (1 : ℤ) [ZMOD (n : ℤ)]) :
    (∀ y : ℤ, (y * 2) ≡ (1 * 2 : ℤ) [ZMOD (n : ℤ)]) := by
  -- 1. proof
  have s1 : ∀ y : ℤ, (y * 2) ≡ (1 * 2 : ℤ) [ZMOD (n : ℤ)] := by
    intro y
    -- 1.1. thm:congruent-times a := y, b := 1, c := 2, from H2
    have s1_1 : (y * 2) ≡ (1 * 2 : ℤ) [ZMOD (n : ℤ)] := by first | exact (Parley.Proofs.Wiedijk.DivisibilityByThree.CongruentTimes.congruent_times (a := y) (b := (1 : ℤ)) (c := (2 : ℤ)) (n := n) (by parley_side) (by parley_side)) | exact ((Parley.Proofs.Wiedijk.DivisibilityByThree.CongruentTimes.congruent_times (a := y) (b := (1 : ℤ)) (c := (2 : ℤ)) (n := n) (by parley_side) (by parley_side))).symm | simpa using (Parley.Proofs.Wiedijk.DivisibilityByThree.CongruentTimes.congruent_times (a := y) (b := (1 : ℤ)) (c := (2 : ℤ)) (n := n) (by parley_side) (by parley_side)) | exact_mod_cast (Parley.Proofs.Wiedijk.DivisibilityByThree.CongruentTimes.congruent_times (a := y) (b := (1 : ℤ)) (c := (2 : ℤ)) (n := n) (by parley_side) (by parley_side)) | (have h := (Parley.Proofs.Wiedijk.DivisibilityByThree.CongruentTimes.congruent_times (a := y) (b := (1 : ℤ)) (c := (2 : ℤ)) (n := n) (by parley_side) (by parley_side)); parley_side)
    all_goals parley_side
  all_goals parley_side

end Parley.Tests.Elaborator.AForAllLineReadInABlock.AForAllLineCitedInABlock
