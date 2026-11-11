module

public import InstanceTactics
public import NormTactics
public import RealTactics
public import Tactics
public import Batteries.Classes.RatCast
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Rat.Init
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Positivity.Basic
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
  have s2 : r / 2 ≠ 0 := by intro h; exact hH2 (by linear_combination (norm := parley_norm) ((4) / ((2))) * h)
  -- 3. thm:irrational-product A := √2, B := r/2, from 1
  have r17_1 : r / 2 ≠ 0 := by exact s2
  have s3 : Irrational (Real.sqrt (2 : ℝ) * ((r : ℝ) / 2)) := by
    have hI : Irrational (Real.sqrt (2 : ℝ) * ((r : ℝ) / 2)) := by parley_instance ((Parley.Proofs.Setmm.RationalClosure.IrrationalProduct.irrational_product (A := Real.sqrt (2 : ℝ)) (B := r / 2) r17_1 s1))
    exact hI
  -- 4. real arithmetic
  have s4 : Real.sqrt (2 : ℝ) * Real.sqrt (2 : ℝ) = 2 := by parley_real
  -- 5. algebra, from 4
  have s5 : (r : ℝ) = Real.sqrt (2 : ℝ) * (Real.sqrt (2 : ℝ) * ((r : ℝ) / 2)) := by linear_combination (norm := parley_norm) ((-(r : ℝ)) / ((2))) * s4
  -- 6. exhibit, from 1, 3, 5
  exact ⟨Real.sqrt (2 : ℝ), Real.sqrt (2 : ℝ) * ((r : ℝ) / 2), ⟨⟨s1, s3⟩, s5⟩⟩

end Parley.Proofs.Hammack.RationalAsIrrationalProduct.RationalAsIrrationalProduct
