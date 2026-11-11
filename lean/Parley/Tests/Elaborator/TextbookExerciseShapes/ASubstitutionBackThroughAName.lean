module

public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Set

/-! Written from tests/elaborator/textbook-exercise-shapes.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.TextbookExerciseShapes.ASubstitutionBackThroughAName

theorem a_substitution_back_through_a_name (a : ℝ) (s : ℝ) (e : ℝ) (hH4 : abs (s - a / 2) < e) :
    abs (s - a / 2) < e := by
  set K : ℝ := a / 2 with hD1
  have hD1_kind : True := by parley_side
  -- 1. substitute K = a/2 (D1) into H4
  have s1 : abs (s - K) < e := by (have h := Eq.subst (motive := (fun t : ℝ => abs (s - t) < e)) hD1.symm hH4; push_cast at h ⊢; all_goals exact_mod_cast h)
  -- 2. substitute K = a/2 (D1) into line 1
  (have h := Eq.subst (motive := (fun t : ℝ => abs (s - t) < e)) hD1 s1; push_cast at h ⊢; all_goals exact_mod_cast h)

end Parley.Tests.Elaborator.TextbookExerciseShapes.ASubstitutionBackThroughAName
