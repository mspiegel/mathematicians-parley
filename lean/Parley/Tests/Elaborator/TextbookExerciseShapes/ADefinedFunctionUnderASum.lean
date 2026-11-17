module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.BigOperators
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from tests/elaborator/textbook-exercise-shapes.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.TextbookExerciseShapes.ADefinedFunctionUnderASum

theorem a_defined_function_under_a_sum (n : ℤ) (hH1 : 0 < n) (t : ℤ → ℤ) (hD1 : ∀ j : ℤ, 0 < j → t j = j + 1) :
    (∑ k ∈ Finset.Icc (1 : ℤ) n, (t k : ℤ)) = (∑ k ∈ Finset.Icc (1 : ℤ) n, (k + 1 : ℤ)) := by
  -- 1. algebra, from D1
  rw [Finset.sum_congr rfl (by intro k h; exact hD1 k (by simp only [Finset.mem_Icc] at h ⊢; omega))]

end Parley.Tests.Elaborator.TextbookExerciseShapes.ADefinedFunctionUnderASum
