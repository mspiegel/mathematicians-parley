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
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Rat.Cast.CharZero
public import Mathlib.Data.Rat.Cast.Defs
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Data.Rat.Init
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Numbers
public import Parley.Proofs.Setmm.RationalClosure.IrrationalProduct
public import Parley.Proofs.Setmm.RationalClosure.IrrationalSum
public import Parley.Proofs.Wiedijk.Sqrt2Irrational.Sqrt2Irrational

/-! Written from proofs/hammack/irrational-between-rationals-by-half-root-two.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.IrrationalBetweenRationalsByHalfRootTwo.IrrationalBetweenRationals

theorem irrational_between_rationals (r : ℚ) (s : ℚ) (hH3 : r < s) :
    (∃ u : ℝ, (Irrational u ∧ (r : ℝ) < u) ∧ u < (s : ℝ)) := by
  -- 1. inequalities
  have s1 : (s - r) / 2 > 0 := by linarith only [hH3]
  -- 2. thm:sqrt2-irrational
  have s2 : Irrational (Real.sqrt (2 : ℝ)) := by exact Parley.Proofs.Wiedijk.Sqrt2Irrational.Sqrt2Irrational.sqrt2_irrational
  -- 3. thm:irrational-product A := √2, B := (s − r)/2, from 2
  have r26_1 : (s - r) / 2 ≠ 0 := ne_of_gt (by linarith only [s1])
  have s3 : Irrational (Real.sqrt (2 : ℝ) * (((s : ℝ) - (r : ℝ)) / 2)) := by
    have hI : Irrational (Real.sqrt (2 : ℝ) * (((s : ℝ) - (r : ℝ)) / 2)) := by parley_instance ((Parley.Proofs.Setmm.RationalClosure.IrrationalProduct.irrational_product (A := Real.sqrt (2 : ℝ)) (B := (s - r) / 2) r26_1 s2))
    exact hI
  -- 4. thm:irrational-sum A := √2·((s − r)/2), B := r, from 3
  have s4 : Irrational (Real.sqrt (2 : ℝ) * (((s : ℝ) - (r : ℝ)) / 2) + (r : ℝ)) := by exact (Parley.Proofs.Setmm.RationalClosure.IrrationalSum.irrational_sum (A := Real.sqrt (2 : ℝ) * (((s : ℝ) - (r : ℝ)) / 2)) (B := r) s3)
  -- 5. real arithmetic
  have s5 : 0 < Real.sqrt (2 : ℝ) := by
    have hf1 : (11 / 8 : ℝ) < Real.sqrt (2 : ℝ) := (Real.lt_sqrt (show (0 : ℝ) ≤ (11 / 8 : ℝ) by norm_num)).mpr (show (11 / 8 : ℝ) ^ 2 < 2 by norm_num)
    have hf2 : Real.sqrt (2 : ℝ) < (23 / 16 : ℝ) := (Real.sqrt_lt' (show (0 : ℝ) < (23 / 16 : ℝ) by norm_num)).mpr (show 2 < (23 / 16 : ℝ) ^ 2 by norm_num)
    linarith only [hf1, hf2]
  -- 6. real arithmetic
  have s6 : Real.sqrt (2 : ℝ) < 2 := by
    have hf1 : (11 / 8 : ℝ) < Real.sqrt (2 : ℝ) := (Real.lt_sqrt (show (0 : ℝ) ≤ (11 / 8 : ℝ) by norm_num)).mpr (show (11 / 8 : ℝ) ^ 2 < 2 by norm_num)
    have hf2 : Real.sqrt (2 : ℝ) < (23 / 16 : ℝ) := (Real.sqrt_lt' (show (0 : ℝ) < (23 / 16 : ℝ) by norm_num)).mpr (show 2 < (23 / 16 : ℝ) ^ 2 by norm_num)
    linarith only [hf1, hf2]
  -- 7. mun:product-positive x := √2, y := (s − r)/2, from 1, 5
  have s7 : Real.sqrt (2 : ℝ) * (((s : ℝ) - (r : ℝ)) / 2) > 0 := by exact (Parley.Items.Stdlib.Numbers.mun_product_positive (x := Real.sqrt (2 : ℝ)) (y := ((s : ℝ) - (r : ℝ)) / 2) s5 (show 0 < ((s : ℝ) - (r : ℝ)) / 2 by have h := (Rat.cast_lt (K := ℝ)).mpr (gt_iff_lt.mp s1); simp only [Rat.cast_sub, Rat.cast_div, Rat.cast_zero, Rat.cast_ofNat] at h; exact h))
  -- 8. mun:less-scaled x := √2, y := 2, c := (s − r)/2, from 1, 6
  have s8 : ((s : ℝ) - (r : ℝ)) / 2 * Real.sqrt (2 : ℝ) < ((s : ℝ) - (r : ℝ)) / 2 * 2 := by exact ((Parley.Items.Stdlib.Numbers.mun_less_scaled (x := Real.sqrt (2 : ℝ)) (y := (2 : ℝ)) (c := ((s : ℝ) - (r : ℝ)) / 2) (show 0 < ((s : ℝ) - (r : ℝ)) / 2 by have h := (Rat.cast_lt (K := ℝ)).mpr (gt_iff_lt.mp s1); simp only [Rat.cast_sub, Rat.cast_div, Rat.cast_zero, Rat.cast_ofNat] at h; exact h))).mp s6
  -- 9. inequalities
  have s9 : (r : ℝ) < Real.sqrt (2 : ℝ) * (((s : ℝ) - (r : ℝ)) / 2) + (r : ℝ) := by linarith only [s7]
  -- 10. inequalities
  have s10 : Real.sqrt (2 : ℝ) * (((s : ℝ) - (r : ℝ)) / 2) + (r : ℝ) < (s : ℝ) := by linarith only [s8]
  -- 11. exhibit, from 4, 9, 10
  exact ⟨Real.sqrt (2 : ℝ) * (((s : ℝ) - (r : ℝ)) / 2) + (r : ℝ), ⟨⟨s4, s9⟩, s10⟩⟩

end Parley.Proofs.Hammack.IrrationalBetweenRationalsByHalfRootTwo.IrrationalBetweenRationals
