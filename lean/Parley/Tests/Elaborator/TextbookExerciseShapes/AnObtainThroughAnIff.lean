module

public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Divisibility

/-! Written from tests/elaborator/textbook-exercise-shapes.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.TextbookExerciseShapes.AnObtainThroughAnIff

theorem an_obtain_through_an_iff (a : ℤ) (r : ℤ) (hH2 : 0 ≤ r) (hH3 : r < 3) (hH4 : a % (3 : ℤ) = r) :
    (∃ q : ℤ, q * 3 + r = a) := by
  -- 1. obtain q: mun:mod-remainder m := 3, from H3, H4
  obtain ⟨q, s1⟩ := ((Parley.Items.Stdlib.Divisibility.mun_mod_remainder (a := a) (m := (3 : ℤ)) (by norm_num) (r := r) hH2 hH3)).mp hH4
  -- 2. exhibit, from 1
  exact ⟨q, s1⟩

end Parley.Tests.Elaborator.TextbookExerciseShapes.AnObtainThroughAnIff
