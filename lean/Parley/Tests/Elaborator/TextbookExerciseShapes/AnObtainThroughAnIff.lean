module

public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Divisibility

/-! Written from tests/elaborator/textbook-exercise-shapes.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.TextbookExerciseShapes.AnObtainThroughAnIff

theorem an_obtain_through_an_iff (a : ℤ) (r : ℤ) (hH2 : 0 ≤ r) (hH3 : r < 3) (hH4 : a % (3 : ℤ) = r) :
    (∃ q : ℤ, q * 3 + r = a) := by
  -- 1. obtain q: mun:mod-remainder m := 3, from H3, H4
  obtain ⟨q, s1⟩ := ((Parley.Items.Stdlib.Divisibility.mun_mod_remainder (a := a) (m := (3 : ℤ)) (by parley_side) (r := r) (by parley_side) hH3)).mp hH4
  -- 2. exhibit, from 1
  exact ⟨q, s1⟩

end Parley.Tests.Elaborator.TextbookExerciseShapes.AnObtainThroughAnIff
