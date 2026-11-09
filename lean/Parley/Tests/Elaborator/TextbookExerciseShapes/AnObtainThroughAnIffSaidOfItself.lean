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

namespace Parley.Tests.Elaborator.TextbookExerciseShapes.AnObtainThroughAnIffSaidOfItself

theorem an_obtain_through_an_iff_said_of_itself (a : ℤ) :
    (∃ q : ℤ, q * 3 + a % (3 : ℤ) = a) := by
  -- 1. mun:mod-natural b := 3
  have s1 : 0 ≤ a % (3 : ℤ) := by exact (Parley.Items.Stdlib.Divisibility.mun_mod_natural (a := a) (b := (3 : ℤ)) (by parley_side))
  -- 2. mun:mod-less b := 3
  have s2 : a % (3 : ℤ) < 3 := by exact (Parley.Items.Stdlib.Divisibility.mun_mod_less (a := a) (b := (3 : ℤ)) (by parley_side))
  -- 3. obtain q: mun:mod-remainder m := 3, r := a mod 3, from 1, 2
  obtain ⟨q, s3⟩ := ((Parley.Items.Stdlib.Divisibility.mun_mod_remainder (a := a) (m := (3 : ℤ)) (by parley_side) (r := a % (3 : ℤ)) (by parley_side) s2)).mp (by parley_side)
  -- 4. exhibit, from 3
  exact ⟨q, s3⟩

end Parley.Tests.Elaborator.TextbookExerciseShapes.AnObtainThroughAnIffSaidOfItself
