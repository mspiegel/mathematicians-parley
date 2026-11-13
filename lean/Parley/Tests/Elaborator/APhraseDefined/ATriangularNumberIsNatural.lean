module

public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
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
public import Parley.Items.Tests.Elaborator.APhraseDefined

/-! Written from tests/elaborator/a-phrase-defined.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.APhraseDefined.ATriangularNumberIsNatural

theorem a_triangular_number_is_natural (x : ℝ) (hH2 : (∃ m : ℤ, 0 < m ∧ (m : ℝ) = x) ∧ (∃ k : ℤ, 0 < k ∧ x = (k : ℝ) * ((k : ℝ) + 1) / 2)) :
    (∃ m : ℤ, 0 < m ∧ (m : ℝ) = x) := by
  -- 1. D1 n := x, from H2
  have s1 : (∃ m : ℤ, 0 < m ∧ (m : ℝ) = x) ∧ (∃ k : ℤ, 0 < k ∧ x = (k : ℝ) * ((k : ℝ) + 1) / 2) := hH2
  -- 2. restate 1
  exact s1.1

end Parley.Tests.Elaborator.APhraseDefined.ATriangularNumberIsNatural
