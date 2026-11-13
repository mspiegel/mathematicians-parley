module

public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Proofs.Wiedijk.DivisibilityByThree.CongruentTimes

/-! Written from tests/elaborator/a-for-all-line-read-in-a-block.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AForAllLineReadInABlock.AForAllLineCitedInABlock

theorem a_for_all_line_cited_in_a_block (n : ℤ) (hH1 : 0 < n) (hH2 : ∀ x : ℤ, x ≡ (1 : ℤ) [ZMOD n]) :
    (∀ y : ℤ, y * 2 ≡ (1 * 2 : ℤ) [ZMOD n]) := by
  -- 1. proof
  intro y
  -- 1.1. thm:congruent-times a := y, b := 1, c := 2, from H2
  exact (Parley.Proofs.Wiedijk.DivisibilityByThree.CongruentTimes.congruent_times (a := y) (b := (1 : ℤ)) (c := (2 : ℤ)) (n := n) hH1 (hH2 y))

end Parley.Tests.Elaborator.AForAllLineReadInABlock.AForAllLineCitedInABlock
