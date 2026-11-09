module

public import NormTactics
public import SubstTactics
public import Tactics
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/identities/sqrt-of-product.proof by parley build lean. -/

public section

namespace Parley.Proofs.Identities.SqrtOfProduct.SqrtOfProduct

theorem sqrt_of_product (a : ℝ) (b : ℝ) (hH3 : a ≥ 0) (hH4 : b ≥ 0) :
    Real.sqrt (a * b) = Real.sqrt a * Real.sqrt b := by
  -- 1. def:sqrt x := a, from H3
  have s1a : Real.sqrt a ≥ 0 := by exact (Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := a) hH3)
  have s1b : Real.sqrt a ^ 2 = a := by exact (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := a) hH3)
  -- 2. def:sqrt x := b, from H4
  have s2a : Real.sqrt b ≥ 0 := by exact (Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := b) hH4)
  have s2b : Real.sqrt b ^ 2 = b := by exact (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := b) hH4)
  -- 3. mun:product-nonneg x := a, y := b, from H3, H4
  have s3 : a * b ≥ 0 := by exact (Parley.Items.Stdlib.Numbers.mun_product_nonneg (x := a) (y := b) (by parley_side) (by parley_side))
  -- 4. def:sqrt x := a·b, from 3
  have s4a : Real.sqrt (a * b) ≥ 0 := by exact (Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := a * b) s3)
  have s4b : Real.sqrt (a * b) ^ 2 = a * b := by exact (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := a * b) s3)
  -- 5. mun:product-nonneg x := √a, y := √b, from 1, 2
  have s5 : Real.sqrt a * Real.sqrt b ≥ 0 := by exact (Parley.Items.Stdlib.Numbers.mun_product_nonneg (x := Real.sqrt a) (y := Real.sqrt b) (by parley_side) (by parley_side))
  -- 6. calculation
  have s6 : (Real.sqrt a * Real.sqrt b) ^ 2 = a * b := by
    calc (Real.sqrt a * Real.sqrt b) ^ 2 = Real.sqrt a ^ 2 * Real.sqrt b ^ 2 := by linear_combination (norm := parley_norm) 0
      _ = a * Real.sqrt b ^ 2 := by parley_subst s1b
      _ = a * b := by parley_subst s2b
  -- 7. calculation
  have s7 : Real.sqrt (a * b) ^ 2 = (Real.sqrt a * Real.sqrt b) ^ 2 := by
    calc Real.sqrt (a * b) ^ 2 = a * b := by parley_side
      _ = (Real.sqrt a * Real.sqrt b) ^ 2 := by parley_side
  -- 8. mun:square-equal x := √(a·b), y := √a·√b, from 1, 2, 4, 5, 7
  exact ((Parley.Items.Stdlib.Numbers.mun_square_equal (x := Real.sqrt (a * b)) (y := Real.sqrt a * Real.sqrt b) (by parley_side) (by parley_side))).mp s7

end Parley.Proofs.Identities.SqrtOfProduct.SqrtOfProduct
