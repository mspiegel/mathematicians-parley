module

public import ArithTactics
public import OrderTactics
public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/elaborator/a-square-root-by-algebra.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ASquareRootByAlgebra.ARootHalvedByInequalities

theorem a_root_halved_by_inequalities :
    0 ≤ Real.sqrt (2 : ℝ) / 2 := by
  -- 1. def:sqrt x := 2
  have r34_1 : (2 : ℤ) ≥ 0 := by parley_arith
  have s1a : Real.sqrt (2 : ℝ) ≥ 0 := (Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := (2 : ℝ)) (by parley_side))
  have s1b : Real.sqrt (2 : ℝ) ^ 2 = 2 := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := (2 : ℝ)) (by parley_side))
  -- 2. inequalities
  parley_order

end Parley.Tests.Elaborator.ASquareRootByAlgebra.ARootHalvedByInequalities
