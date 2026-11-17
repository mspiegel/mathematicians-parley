module

public import Mathlib.Analysis.Complex.Order
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.TypeStar

/-! Written from tests/elaborator/a-value-a-cited-equation-says-is-a-number.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AValueACitedEquationSaysIsANumber.AValueEquatedForInequalities

theorem a_value_equated_for_inequalities {α : Type*} [Nonempty α] (D : Set α) (E : Set ℂ) (f : α → ℂ) (hH3 : Set.MapsTo f D E) (c : α) (hH4 : c ∈ D) (x : ℝ) (hH6 : f c = 1) (hH7 : x = 2) :
    (x : ℂ) + f c = 3 := by
  -- 1. inequalities, from H6, H7
  linarith only [hH6, (show (x : ℂ) = 2 by exact_mod_cast hH7)]

end Parley.Tests.Elaborator.AValueACitedEquationSaysIsANumber.AValueEquatedForInequalities
