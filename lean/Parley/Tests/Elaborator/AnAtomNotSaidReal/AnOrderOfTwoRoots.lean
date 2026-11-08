module

public import OrderTactics
public import Tactics
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/elaborator/an-atom-not-said-real.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AnAtomNotSaidReal.AnOrderOfTwoRoots

theorem an_order_of_two_roots (A : ℝ) (B : ℝ) (hH3 : 0 ≤ A) (hH4 : 0 ≤ B) (hH5 : ¬ Real.sqrt A ≤ Real.sqrt B) :
    Real.sqrt B < Real.sqrt A := by
  -- 1. def:sqrt x := A, from H3
  have s1a : Real.sqrt A ≥ 0 := (Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := A) hH3)
  have s1b : Real.sqrt A ^ 2 = A := by exact (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := A) hH3)
  -- 2. def:sqrt x := B, from H4
  have s2a : Real.sqrt B ≥ 0 := (Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := B) hH4)
  have s2b : Real.sqrt B ^ 2 = B := by exact (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := B) hH4)
  -- 3. inequalities, from H5
  parley_order

end Parley.Tests.Elaborator.AnAtomNotSaidReal.AnOrderOfTwoRoots
