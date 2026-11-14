module

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
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Tests.Elaborator.ADefineFillingACitedFunction.ValueAtOne

/-! Written from tests/elaborator/a-define-filling-a-cited-function.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ADefineFillingACitedFunction.ADefineFillingACitedFunction

theorem a_define_filling_a_cited_function (t : ℤ → ℤ) (hD1 : ∀ j : ℤ, 0 < j → t j = j + 1) :
    t 1 = 1 + 1 := by
  -- 1. D1
  have s1 : ∀ j : ℤ, 0 < j → t j = j + 1 := by intro j h_j; simp (disch := omega) only [hD1 j h_j]
  -- 2. thm:value-at-one f := t, from 1
  have hI : t 1 = 1 + 1 := by exact_mod_cast ((Parley.Tests.Elaborator.ADefineFillingACitedFunction.ValueAtOne.value_at_one (f := (fun x : ℤ => ((t (x : ℤ) : ℤ) : ℝ))) (by intro k h_k; exact_mod_cast s1 k h_k)))
  exact hI

end Parley.Tests.Elaborator.ADefineFillingACitedFunction.ADefineFillingACitedFunction
