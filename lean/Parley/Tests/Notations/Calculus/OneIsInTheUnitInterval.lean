module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Calculus

/-! Written from tests/notations/calculus.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Calculus.OneIsInTheUnitInterval

theorem one_is_in_the_unit_interval :
    (1 : ℝ) ∈ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ) := by
  -- 1. def:interval a := 0, b := 1, x := 1
  have r164_1 : (0 : ℤ) ≤ 1 := by norm_num
  have r164_2 : (1 : ℤ) ≤ 1 := by norm_num
  exact ((Parley.Items.Stdlib.Calculus.def_interval (x := (1 : ℝ)) (a := (0 : ℝ)) (b := (1 : ℝ)))).mpr ⟨⟨by trivial, by norm_num⟩, by norm_num⟩

end Parley.Tests.Notations.Calculus.OneIsInTheUnitInterval
