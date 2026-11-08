module

public import AlgebraTactics
public import Tactics
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic

/-! Written from tests/elaborator/textbook-exercise-shapes.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.TextbookExerciseShapes.AnExponentWithoutItsOne

theorem an_exponent_without_its_one (d : ℤ) (hH1 : 0 < d) :
    (2 ^ (d * 1).toNat : ℤ) = 2 ^ d.toNat := by
  -- 1. algebra
  parley_ring

end Parley.Tests.Elaborator.TextbookExerciseShapes.AnExponentWithoutItsOne
