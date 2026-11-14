module

public import InstanceTactics
public import Batteries.Classes.RatCast
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Rat.Init
public import Mathlib.NumberTheory.Real.Irrational
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
public import Parley.Proofs.Setmm.RationalClosure.IrrationalProduct
public import Parley.Proofs.Wiedijk.Sqrt2Irrational.Sqrt2Irrational

/-! Written from proofs/hammack/rational-as-irrational-product.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.RationalAsIrrationalProduct.RationalAsIrrationalProduct

theorem rational_as_irrational_product (r : ℚ) (hH2 : r ≠ 0) :
    (∃ x : ℝ, ∃ y : ℝ, (Irrational x ∧ Irrational y) ∧ (r : ℝ) = x * y) := by
  -- 1. thm:sqrt2-irrational
  have s1 : Irrational (Real.sqrt (2 : ℝ)) := by exact Parley.Proofs.Wiedijk.Sqrt2Irrational.Sqrt2Irrational.sqrt2_irrational
  -- 2. algebra, from H2
  have s2 : r / 2 ≠ 0 := by intro h; exact hH2 (by linear_combination ((4) / (((2 : ℚ)))) * h)
  -- 3. thm:irrational-product A := √2, B := r/2, from 1
  have r17_1 : r / 2 ≠ 0 := by exact s2
  have s3 : Irrational (Real.sqrt (2 : ℝ) * ((r : ℝ) / 2)) := by
    have hI : Irrational (Real.sqrt (2 : ℝ) * ((r : ℝ) / 2)) := by parley_instance ((Parley.Proofs.Setmm.RationalClosure.IrrationalProduct.irrational_product (A := Real.sqrt (2 : ℝ)) (B := r / 2) r17_1 s1))
    exact hI
  -- 4. real arithmetic
  have s4 : Real.sqrt (2 : ℝ) * Real.sqrt (2 : ℝ) = 2 := by
    have hr2 : Real.sqrt (2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    linear_combination hr2
  -- 5. algebra, from 4
  have s5 : (r : ℝ) = Real.sqrt (2 : ℝ) * (Real.sqrt (2 : ℝ) * ((r : ℝ) / 2)) := by linear_combination ((-(r : ℝ)) / (((2 : ℝ)))) * s4
  -- 6. exhibit, from 1, 3, 5
  exact ⟨Real.sqrt (2 : ℝ), Real.sqrt (2 : ℝ) * ((r : ℝ) / 2), ⟨⟨s1, s3⟩, s5⟩⟩

end Parley.Proofs.Hammack.RationalAsIrrationalProduct.RationalAsIrrationalProduct
