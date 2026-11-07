module

public import OrderTactics
public import SetTactics
public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq

/-! Written from tests/elaborator/sets-a-define-names.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.SetsADefineNames.ValuesOfAOneToOneFunction

theorem values_of_a_one_to_one_function (n : ℤ) (hH1 : 0 < n) (a : ℤ → ℝ) (hH2 : Set.MapsTo a (Set.Icc (1 : ℤ) n : Set ℤ) (Set.univ : Set ℝ) ∧ Set.InjOn a (Set.Icc (1 : ℤ) n : Set ℤ)) (k : ℤ) (hH3 : k ∈ Finset.Icc (1 : ℤ) n) :
    a k ≤ a k := by
  -- 1. inequalities
  have s1 : a k ≤ a k := by parley_order
  all_goals exact s1

end Parley.Tests.Elaborator.SetsADefineNames.ValuesOfAOneToOneFunction
