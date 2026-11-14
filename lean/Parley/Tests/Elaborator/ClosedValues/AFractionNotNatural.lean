module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Rat.Init
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from tests/elaborator/closed-values.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ClosedValues.AFractionNotNatural

theorem a_fraction_not_natural :
    ¬ (∃ m : ℤ, 0 < m ∧ (m : ℚ) = 1 / 76) := by
  -- 1. arithmetic
  rintro ⟨m, _, h⟩; field_simp at h; norm_cast at h; omega

end Parley.Tests.Elaborator.ClosedValues.AFractionNotNatural
