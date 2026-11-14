module

public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Ring.RingNF

/-! Written from tests/elaborator/a-for-all-line-read-in-a-block.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AForAllLineReadInABlock.AForAllLineJoinedInABlock

theorem a_for_all_line_joined_in_a_block :
    (∀ z : ℤ, z * 1 = z) := by
  -- 1. proof
  have s1 : ∀ x : ℤ, x * 1 = x := by
    intro x
    -- 1.1. algebra
    ring_nf
  -- 2. proof
  intro z
  -- 2.1. restate 1
  exact (s1 z)

end Parley.Tests.Elaborator.AForAllLineReadInABlock.AForAllLineJoinedInABlock
