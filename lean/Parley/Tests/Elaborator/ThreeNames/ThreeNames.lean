module

public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from tests/elaborator/three-names.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ThreeNames.ThreeNames

theorem three_names (hH1 : ∃ a : ℤ, 0 < a ∧ (∃ b : ℤ, 0 < b ∧ (∃ c : ℤ, 0 < c ∧ a + 2 * b + 3 * c = 6))) :
    (∃ a : ℤ, 0 < a ∧ (∃ b : ℤ, 0 < b ∧ (∃ c : ℤ, 0 < c ∧ 3 * c + 2 * b + a = 6))) := by
  -- 1. obtain a, b, c from H1
  obtain ⟨a, s1a, b, s1b, c, s1c, s1d⟩ := hH1
  -- 2. algebra, from 1
  have s2 : 3 * c + 2 * b + a = 6 := by linear_combination s1d
  -- 3. exhibit, from 2
  exact ⟨a, s1a, b, s1b, c, s1c, s2⟩

end Parley.Tests.Elaborator.ThreeNames.ThreeNames
