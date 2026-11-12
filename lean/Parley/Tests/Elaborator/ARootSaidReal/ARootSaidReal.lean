module

public import Tactics
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Order.Basic
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/elaborator/a-root-said-real.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ARootSaidReal.ARootSaidReal

theorem a_root_said_real (A : ℝ) (hH2 : A ≥ 0) :
    Real.sqrt A ^ 2 ≤ A + 1 := by
  -- 1. def:sqrt x := A, from H2
  have s1 : Real.sqrt A ^ 2 = A := by exact (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := A) hH2)
  -- 2. inequalities
  have s2 : A ≤ A + 1 := by linarith
  -- 3. transitivity, from 1, 2
  exact Eq.trans_le s1 s2

end Parley.Tests.Elaborator.ARootSaidReal.ARootSaidReal
