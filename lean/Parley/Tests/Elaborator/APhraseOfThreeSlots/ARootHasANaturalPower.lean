module

public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Tests.Elaborator.APhraseOfThreeSlots

/-! Written from tests/elaborator/a-phrase-of-three-slots.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.APhraseOfThreeSlots.ARootHasANaturalPower

theorem a_root_has_a_natural_power (x : ℝ) (m : ℤ) (hH3 : 0 < m ∧ x ^ m = 1) :
    0 < m := by
  -- 1. D1 z := x, n := m, w := 1, from H3
  have s1 : 0 < m ∧ x ^ m = 1 := hH3
  -- 2. restate 1
  exact s1.1

end Parley.Tests.Elaborator.APhraseOfThreeSlots.ARootHasANaturalPower
