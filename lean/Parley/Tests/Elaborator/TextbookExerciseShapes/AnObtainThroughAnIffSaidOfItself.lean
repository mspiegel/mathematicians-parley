module

public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Order.Defs.PartialOrder
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

namespace Parley.Tests.Elaborator.TextbookExerciseShapes.AnObtainThroughAnIffSaidOfItself

theorem an_obtain_through_an_iff_said_of_itself (a : ℤ) :
    (∃ q : ℤ, q * 3 + a % (3 : ℤ) = a) := by
  -- 1. mun:mod-less b := 3
  have s1 : a % (3 : ℤ) < 3 := by exact (Parley.Items.Stdlib.Divisibility.mun_mod_less (a := a) (b := (3 : ℤ)) (by norm_num))
  -- 2. obtain q: mun:mod-remainder m := 3, r := a mod 3, from 1
  obtain ⟨q, s2⟩ := ((Parley.Items.Stdlib.Divisibility.mun_mod_remainder (a := a) (m := (3 : ℤ)) (by norm_num) (r := a % (3 : ℤ)) (Int.emod_nonneg _ (ne_of_gt (by norm_num))) s1)).mp rfl
  -- 3. exhibit, from 2
  exact ⟨q, s2⟩

end Parley.Tests.Elaborator.TextbookExerciseShapes.AnObtainThroughAnIffSaidOfItself
