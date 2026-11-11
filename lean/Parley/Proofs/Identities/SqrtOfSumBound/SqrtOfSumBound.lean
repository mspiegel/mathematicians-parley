module

public import NormTactics
public import OrderTactics
public import Tactics
public import Mathlib.Algebra.Group.Monoid
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

/-! Written from proofs/identities/sqrt-of-sum-bound.proof by parley build lean. -/

public section

namespace Parley.Proofs.Identities.SqrtOfSumBound.SqrtOfSumBound

theorem sqrt_of_sum_bound (a : ℝ) (b : ℝ) (hH3 : a ≥ 0) (hH4 : b ≥ 0) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  -- 1. def:sqrt x := a, from H3
  have s1a : Real.sqrt a ≥ 0 := by exact (Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := a) hH3)
  have s1b : Real.sqrt a ^ 2 = a := by exact (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := a) hH3)
  -- 2. def:sqrt x := b, from H4
  have s2a : Real.sqrt b ≥ 0 := by exact (Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := b) hH4)
  have s2b : Real.sqrt b ^ 2 = b := by exact (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := b) hH4)
  -- 3. inequalities, from H3, H4
  have s3 : a + b ≥ 0 := by parley_order
  -- 4. def:sqrt x := a + b, from 3
  have s4a : Real.sqrt (a + b) ≥ 0 := by exact (Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := a + b) s3)
  have s4b : Real.sqrt (a + b) ^ 2 = a + b := by exact (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := a + b) s3)
  -- 5. inequalities, from 1, 2
  have s5 : Real.sqrt a + Real.sqrt b ≥ 0 := by parley_order
  -- 6. mun:product-nonneg x := √a, y := √b, from 1, 2
  have s6 : Real.sqrt a * Real.sqrt b ≥ 0 := by exact (Parley.Items.Stdlib.Numbers.mun_product_nonneg (x := Real.sqrt a) (y := Real.sqrt b) s1a s2a)
  -- 7. inequalities
  have s7 : a + b ≤ a + b + 2 * (Real.sqrt a * Real.sqrt b) := by parley_order
  -- 8. calculation
  have s8 : Real.sqrt (a + b) ^ 2 ≤ (Real.sqrt a + Real.sqrt b) ^ 2 := by
    calc Real.sqrt (a + b) ^ 2 = a + b := by exact s4b
      _ ≤ a + b + 2 * (Real.sqrt a * Real.sqrt b) := by exact s7
      _ = (Real.sqrt a + Real.sqrt b) ^ 2 := by linear_combination (norm := parley_norm) (-1) * s1b + (-1) * s2b
  -- 9. mun:square-le x := √(a + b), y := √a + √b, from 1, 2, 4, 5, 8
  exact ((Parley.Items.Stdlib.Numbers.mun_square_le (x := Real.sqrt (a + b)) (y := Real.sqrt a + Real.sqrt b) s4a s5)).mpr s8

end Parley.Proofs.Identities.SqrtOfSumBound.SqrtOfSumBound
