module

public import AlgebraTactics
public import OrderTactics
public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/elaborator/a-requires-weakening-with-its-membership.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ARequiresWeakeningWithItsMembership.ARequiresWeakeningWithItsMembership

theorem a_requires_weakening_with_its_membership (x : ℝ) (hH2 : x ≥ 0) :
    Real.sqrt (x + 1) - Real.sqrt x = 1 / (Real.sqrt (x + 1) + Real.sqrt x) := by
  -- 1. inequalities, from H2
  have s1 : x + 1 ≥ 0 := by parley_order
  -- 2. def:sqrt x := x + 1, from 1
  have s2a : Real.sqrt (x + 1) ≥ 0 := by exact (Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := x + 1) s1)
  have s2b : Real.sqrt (x + 1) ^ 2 = x + 1 := by exact (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := x + 1) s1)
  -- 3. def:sqrt, from H2
  have s3a : Real.sqrt x ≥ 0 := by exact (Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := x) hH2)
  have s3b : Real.sqrt x ^ 2 = x := by exact (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := x) hH2)
  -- 4. inequalities
  have s4 : x < x + 1 := by parley_order
  -- 5. calculation
  have s5 : Real.sqrt x ^ 2 < Real.sqrt (x + 1) ^ 2 := by
    calc Real.sqrt x ^ 2 = x := by exact s3b
      _ < x + 1 := by exact s4
      _ = Real.sqrt (x + 1) ^ 2 := by exact s2b.symm
  -- 6. mun:square-less x := √x, y := √(x + 1), from 2, 3, 5
  have s6 : Real.sqrt x < Real.sqrt (x + 1) := ((Parley.Items.Stdlib.Numbers.mun_square_less (x := Real.sqrt x) (y := Real.sqrt (x + 1)) (by parley_side) (by parley_side))).mpr s5
  -- 7. transitivity, from 3, 6
  have s7 : Real.sqrt (x + 1) > 0 := by parley_order
  -- 8. inequalities, from 2, 3, 7
  have s8 : Real.sqrt (x + 1) + Real.sqrt x > 0 := by parley_order
  -- 9. algebra, from 2, 3
  have r40_3 : Real.sqrt (x + 1) + Real.sqrt x ≠ 0 := by parley_side
  linear_combination (norm := parley_field) ((1) / ((Real.sqrt (x + 1) + Real.sqrt x))) * s2b + ((-1) / ((Real.sqrt (x + 1) + Real.sqrt x))) * s3b

end Parley.Tests.Elaborator.ARequiresWeakeningWithItsMembership.ARequiresWeakeningWithItsMembership
