module

public import AlgebraTactics
public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic

/-! Written from tests/elaborator/a-for-all-line-read-in-a-block.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AForAllLineReadInABlock.AForAllLineJoinedInABlock

theorem a_for_all_line_joined_in_a_block :
    (∀ z : ℤ, z * 1 = z) := by
  -- 1. proof
  have s1 : ∀ x : ℤ, x * 1 = x := by
    intro x
    -- 1.1. algebra
    parley_ring
  -- 2. proof
  intro z
  -- 2.1. restate 1
  parley_side

end Parley.Tests.Elaborator.AForAllLineReadInABlock.AForAllLineJoinedInABlock
