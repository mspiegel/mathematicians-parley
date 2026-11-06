module

public import RealTactics
public import Tactics
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Rat.Init
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Tactic.LinearCombination
public import Parley.Proofs.Setmm.RationalClosure.IrrationalProduct
public import Parley.Proofs.Wiedijk.Sqrt2Irrational.Sqrt2Irrational

/-! Written from proofs/hammack/rational-as-irrational-product.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.RationalAsIrrationalProduct.RationalAsIrrationalProduct

theorem rational_as_irrational_product (r : ℚ) (hH2 : r ≠ 0) :
    (∃ x : ℝ, ∃ y : ℝ, (Irrational x ∧ Irrational y) ∧ (r : ℝ) = x * y) := by
  -- 1. thm:sqrt2-irrational
  have s1 : Irrational (Real.sqrt (2 : ℝ)) := by first | exact Parley.Proofs.Wiedijk.Sqrt2Irrational.Sqrt2Irrational.sqrt2_irrational | exact (Parley.Proofs.Wiedijk.Sqrt2Irrational.Sqrt2Irrational.sqrt2_irrational).symm | simpa using Parley.Proofs.Wiedijk.Sqrt2Irrational.Sqrt2Irrational.sqrt2_irrational | exact_mod_cast Parley.Proofs.Wiedijk.Sqrt2Irrational.Sqrt2Irrational.sqrt2_irrational | (have h := Parley.Proofs.Wiedijk.Sqrt2Irrational.Sqrt2Irrational.sqrt2_irrational; parley_side)
  -- 2. algebra, from H2
  have s2 : r / 2 ≠ 0 := by intro h; exact hH2 (by linear_combination (norm := parley_norm) ((4) / ((2))) * h)
  -- 3. thm:irrational-product A := √2, B := r/2, from 1
  have r17_1 : r / 2 ≠ 0 := by parley_side
  have s3 : Irrational (Real.sqrt (2 : ℝ) * ((r : ℝ) / 2)) := by first | exact (Parley.Proofs.Setmm.RationalClosure.IrrationalProduct.irrational_product (A := Real.sqrt (2 : ℝ)) (B := r / 2) (by parley_side) s1) | exact ((Parley.Proofs.Setmm.RationalClosure.IrrationalProduct.irrational_product (A := Real.sqrt (2 : ℝ)) (B := r / 2) (by parley_side) s1)).symm | simpa using (Parley.Proofs.Setmm.RationalClosure.IrrationalProduct.irrational_product (A := Real.sqrt (2 : ℝ)) (B := r / 2) (by parley_side) s1) | exact_mod_cast (Parley.Proofs.Setmm.RationalClosure.IrrationalProduct.irrational_product (A := Real.sqrt (2 : ℝ)) (B := r / 2) (by parley_side) s1) | (have h := (Parley.Proofs.Setmm.RationalClosure.IrrationalProduct.irrational_product (A := Real.sqrt (2 : ℝ)) (B := r / 2) (by parley_side) s1); parley_rat_of_real h) | (have h := (Parley.Proofs.Setmm.RationalClosure.IrrationalProduct.irrational_product (A := Real.sqrt (2 : ℝ)) (B := r / 2) (by parley_side) s1); parley_side)
  -- 4. real arithmetic
  have s4 : Real.sqrt (2 : ℝ) * Real.sqrt (2 : ℝ) = 2 := by parley_real
  -- 5. algebra, from 4
  have s5 : (r : ℝ) = Real.sqrt (2 : ℝ) * (Real.sqrt (2 : ℝ) * ((r : ℝ) / 2)) := by linear_combination (norm := parley_norm) ((-(r : ℝ)) / ((2))) * s4
  -- 6. exhibit, from 1, 3, 5
  have s6 : ∃ x : ℝ, ∃ y : ℝ, (Irrational x ∧ Irrational y) ∧ (r : ℝ) = x * y := ⟨Real.sqrt (2 : ℝ), Real.sqrt (2 : ℝ) * ((r : ℝ) / 2), ⟨⟨by parley_side, by parley_side⟩, by parley_side⟩⟩
  all_goals exact s6

end Parley.Proofs.Hammack.RationalAsIrrationalProduct.RationalAsIrrationalProduct
