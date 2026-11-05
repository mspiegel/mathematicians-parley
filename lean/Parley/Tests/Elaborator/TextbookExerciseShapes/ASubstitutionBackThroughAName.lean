module

public import SubstTactics
public import Tactics

/-! Written from tests/elaborator/textbook-exercise-shapes.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.TextbookExerciseShapes.ASubstitutionBackThroughAName

theorem a_substitution_back_through_a_name (a : ℝ) (s : ℝ) (e : ℝ) (hH4 : abs (s - a / 2) < e) :
    abs (s - a / 2) < e := by
  set K : ℝ := a / 2 with hD1
  have hD1_kind : True := by parley_side
  -- 1. substitute K = a/2 (D1) into H4
  have s1 : abs (s - K) < e := by parley_subst_at hD1 hH4
  -- 2. substitute K = a/2 (D1) into line 1
  have s2 : abs (s - a / 2) < e := by parley_subst_at hD1 s1
  all_goals exact s2

end Parley.Tests.Elaborator.TextbookExerciseShapes.ASubstitutionBackThroughAName
