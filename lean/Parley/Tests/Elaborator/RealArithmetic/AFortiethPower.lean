module

public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Nat.Notation
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from tests/elaborator/real-arithmetic.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmetic.AFortiethPower

theorem a_fortieth_power :
    (1 + Real.sqrt (2 : ℝ)) ^ 40 = 1023286908188737 + 723573111879672 * Real.sqrt (2 : ℝ) := by
  -- 1. real arithmetic
  have hr2 : Real.sqrt (2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  linear_combination (Real.sqrt (2 : ℝ) ^ 38 + 40 * Real.sqrt (2 : ℝ) ^ 37 + 782 * Real.sqrt (2 : ℝ) ^ 36 + 9960 * Real.sqrt (2 : ℝ) ^ 35 + 92954 * Real.sqrt (2 : ℝ) ^ 34 + 677928 * Real.sqrt (2 : ℝ) ^ 33 + 4024288 * Real.sqrt (2 : ℝ) ^ 32 + 19999416 * Real.sqrt (2 : ℝ) ^ 31 + 84953261 * Real.sqrt (2 : ℝ) ^ 30 + 313437712 * Real.sqrt (2 : ℝ) ^ 29 + 1017567050 * Real.sqrt (2 : ℝ) ^ 28 + 2938676864 * Real.sqrt (2 : ℝ) ^ 27 + 7621987580 * Real.sqrt (2 : ℝ) ^ 26 + 17910576608 * Real.sqrt (2 : ℝ) ^ 25 + 38450905000 * Real.sqrt (2 : ℝ) ^ 24 + 76046498272 * Real.sqrt (2 : ℝ) ^ 23 + 139753911650 * Real.sqrt (2 : ℝ) ^ 22 + 240825375344 * Real.sqrt (2 : ℝ) ^ 21 + 392888085100 * Real.sqrt (2 : ℝ) ^ 20 + 612933159088 * Real.sqrt (2 : ℝ) ^ 19 + 923622699020 * Real.sqrt (2 : ℝ) ^ 18 + 1357148726576 * Real.sqrt (2 : ℝ) ^ 17 + 1960625659840 * Real.sqrt (2 : ℝ) ^ 16 + 2803029831952 * Real.sqrt (2 : ℝ) ^ 15 + 3984103421330 * Real.sqrt (2 : ℝ) ^ 14 + 5646285008960 * Real.sqrt (2 : ℝ) ^ 13 + 7991413772500 * Real.sqrt (2 : ℝ) ^ 12 + 11304603240800 * Real.sqrt (2 : ℝ) ^ 11 + 15988414398480 * Real.sqrt (2 : ℝ) ^ 10 + 22611518283040 * Real.sqrt (2 : ℝ) ^ 9 + 31977676457488 * Real.sqrt (2 : ℝ) ^ 8 + 45223310004960 * Real.sqrt (2 : ℝ) ^ 7 + 63955429819661 * Real.sqrt (2 : ℝ) ^ 6 + 90446638653480 * Real.sqrt (2 : ℝ) ^ 5 + 127910863477702 * Real.sqrt (2 : ℝ) ^ 4 + 180893277964968 * Real.sqrt (2 : ℝ) ^ 3 + 255821727046794 * Real.sqrt (2 : ℝ) ^ 2 + 361786555939816 * Real.sqrt (2 : ℝ) + 511643454094368) * hr2

end Parley.Tests.Elaborator.RealArithmetic.AFortiethPower
