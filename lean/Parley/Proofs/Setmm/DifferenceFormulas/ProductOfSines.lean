module

public import NormTactics
public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Trigonometry
public import Parley.Proofs.Setmm.DifferenceFormulas.CosineOfDifference

/-! Written from proofs/setmm/difference-formulas.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.DifferenceFormulas.ProductOfSines

theorem product_of_sines (A : ℂ) (B : ℂ) :
    Complex.sin A * Complex.sin B = (Complex.cos (A - B) - Complex.cos (A + B)) / 2 := by
  -- 1. thm:cosine-of-difference
  have s1 : Complex.cos (A - B) = Complex.cos A * Complex.cos B + Complex.sin A * Complex.sin B := by exact (Parley.Proofs.Setmm.DifferenceFormulas.CosineOfDifference.cosine_of_difference (A := A) (B := B))
  -- 2. thm:cos-add a := A, b := B
  have s2 : Complex.cos (A + B) = Complex.cos A * Complex.cos B - Complex.sin A * Complex.sin B := by exact (Parley.Items.Stdlib.Trigonometry.thm_cos_add (a := A) (b := B))
  -- 3. algebra, from 1, 2
  have s3 : Complex.sin A * Complex.sin B = (Complex.cos (A - B) - Complex.cos (A + B)) / 2 := by linear_combination (norm := parley_norm) ((-1) / ((2))) * s1 + ((1) / ((2))) * s2
  all_goals exact s3

end Parley.Proofs.Setmm.DifferenceFormulas.ProductOfSines
