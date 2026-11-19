module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.AddTorsor
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Reasoning

/-! Written from tests/elaborator/a-value-with-a-comma.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AValueWithAComma.AValueWithACommaLast

theorem a_value_with_a_comma_last (A : ℂ) (B : ℂ) (C : ℂ) (x : ℝ) (hH5 : x = 1 ↔ Collinear ℝ {A, B, C}) (hH6 : ¬ Collinear ℝ {A, B, C}) :
    x ≠ 1 := by
  -- 1. mun:iff-not-from-right P := x = 1, Q := A, B, C are collinear, from H5, H6
  exact (Parley.Items.Stdlib.Reasoning.mun_iff_not_from_right (P := x = 1) (Q := Collinear ℝ {A, B, C}) hH5 hH6)

end Parley.Tests.Elaborator.AValueWithAComma.AValueWithACommaLast
