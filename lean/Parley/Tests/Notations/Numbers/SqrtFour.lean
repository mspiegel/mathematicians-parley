module

public import ArithTactics
public import Tactics
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/notations/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Numbers.SqrtFour

theorem sqrt_four :
    Real.sqrt (4 : ℝ) = 2 := by
  -- 1. def:sqrt x := 4
  have r88_1 : (4 : ℤ) ≥ 0 := by parley_arith
  have s1a : Real.sqrt (4 : ℝ) ^ 2 = 4 := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := (4 : ℝ)) (by parley_side))
  have s1b : Real.sqrt (4 : ℝ) ≥ 0 := (Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := (4 : ℝ)) (by parley_side))
  -- 2. calculation
  have s2 : Real.sqrt (4 : ℝ) ^ 2 = 2 ^ 2 := by
    calc Real.sqrt (4 : ℝ) ^ 2 = 4 := by parley_side
      _ = 2 ^ 2 := by norm_num
  -- 3. mun:square-equal x := √4, y := 2, from 2
  have r97_1 : Real.sqrt (4 : ℝ) ≥ 0 := by parley_side
  have r97_2 : (2 : ℤ) ≥ 0 := by parley_arith
  exact ((Parley.Items.Stdlib.Numbers.mun_square_equal (x := Real.sqrt (4 : ℝ)) (y := (2 : ℝ)) (by parley_side) (by parley_side))).mp s2

end Parley.Tests.Notations.Numbers.SqrtFour
