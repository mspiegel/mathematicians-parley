module

public import Tactics
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic

/-! Written from tests/elaborator/an-instance-without-its-zero.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AnInstanceWithoutItsZero.AnInstanceWithoutItsZero

theorem an_instance_without_its_zero (a : ℤ → ℝ) (hH2 : ∀ k : ℤ, 0 ≤ k → a (k + 1) = a k + 2) :
    a 1 = a 0 + 2 := by
  -- 1. instantiate k := 0 in H2
  simpa only [zero_add] using (hH2 (0 : ℤ) (by parley_side))

end Parley.Tests.Elaborator.AnInstanceWithoutItsZero.AnInstanceWithoutItsZero
