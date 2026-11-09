module

public import ArithTactics
public import NormTactics
public import OrderTactics
public import PowerTactics
public import RealTactics
public import SubstTactics
public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Rat.Init
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring.RingNF
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Numbers
public import Parley.Proofs.Hammack.Sqrt3Irrational.Sqrt3Irrational
public import Parley.Proofs.Setmm.RationalClosure.IrrationalProduct

/-! Written from proofs/hammack/sqrt-of-odd-power-of-three.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.SqrtOfOddPowerOfThree.SqrtOfOddPowerOfThree

set_option maxHeartbeats 400000 in
theorem sqrt_of_odd_power_of_three (k : ℤ) (hH1 : 0 < k) (hH2 : Odd k) :
    Irrational (Real.sqrt (3 ^ k.toNat : ℝ)) := by
  -- 1. obtain m: def:odd n := k, from H2
  obtain ⟨m, s1⟩ := ((Parley.Items.Stdlib.Divisibility.def_odd (n := k))).mp hH2
  -- 2. inequalities, from H1
  have s2 : 1 ≤ k := by parley_order
  -- 3. substitute k = 2m + 1 (line 1) into line 2
  have s3 : 1 ≤ 2 * m + 1 := by parley_subst_at s1 s2
  -- 4. inequalities
  have s4 : 0 ≤ m := by parley_order
  -- 5. mun:nat0-as-int n := m, from 4
  have s5 : 0 ≤ m := by simpa only [Int.cast_id, exists_eq_right] using ((Parley.Items.Stdlib.Numbers.mun_nat0_as_int (n := m))).mpr (by parley_side)
  -- 6. mun:power-nat a := 3, from 5
  have s6 : ∃ m₀ : ℤ, 0 < m₀ ∧ (m₀ : ℚ) = 3 ^ m := by
    have whole1 : ((3 : ℚ) : ℚ) ^ (m).toNat = (3 ^ m : ℚ) := by rw [← zpow_natCast, Int.toNat_of_nonneg s5]
    refine ⟨(((3 : ℤ) ^ (m).toNat) : ℤ), ?_, by first | (push_cast; simp only [whole1]; done) | (push_cast; simp only [whole1]; ring)⟩
    (exact (Parley.Items.Stdlib.Numbers.mun_power_nat (a := (3 : ℤ)) (by parley_side) (m := m) (by parley_side)))
  -- 7. mun:power-nat a := 3, m := k
  have s7 : (0 : ℤ) < 3 ^ k.toNat := by exact (Parley.Items.Stdlib.Numbers.mun_power_nat (a := (3 : ℤ)) (by parley_side) (m := k) (by parley_side))
  -- 8. algebra, from 1
  have s8 : k = m + m + 1 := by linear_combination (norm := parley_norm) s1
  -- 9. mun:exponent-sum a := 3, n := m, from 5
  have s9 : (3 ^ (m + m) : ℚ) = 3 ^ m * 3 ^ m := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_exponent_sum (a := (3 : ℚ)) (m := m) (by parley_side) (n := m) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_sum (a := (3 : ℚ)) (m := m) (by parley_side) (n := m) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_sum (a := (3 : ℚ)) (m := m) (by parley_side) (n := m) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_exponent_sum (a := (3 : ℚ)) (m := m) (by parley_side) (n := m) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_exponent_sum (a := (3 : ℚ)) (m := m) (by parley_side) (n := m) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_sum (a := (3 : ℚ)) (m := m) (by parley_side) (n := m) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_sum (a := (3 : ℚ)) (m := m) (by parley_side) (n := m) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_sum (a := (3 : ℚ)) (m := m) (by parley_side) (n := m) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_sum (a := (3 : ℚ)) (m := m) (by parley_side) (n := m) (by parley_side)); parley_side)
  -- 10. calculation
  have r50_1 : 0 ≤ m + m := by parley_side
  have s10 : (3 ^ k.toNat : ℚ) = 3 ^ m * 3 ^ m * 3 := by
    calc (3 ^ k.toNat : ℚ) = 3 ^ (m + m + 1) := by
          have s8_w : (k : ℚ) = (m : ℚ) + (m : ℚ) + 1 := by have h := congrArg (fun x : ℤ => (x : ℚ)) s8; push_cast at h; linear_combination (norm := parley_norm) h
          first | parley_subst s8_w | parley_subst s8
      _ = 3 ^ (m + m) * 3 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (3 : ℚ)) (m := m + m) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (3 : ℚ)) (m := m + m) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (3 : ℚ)) (m := m + m) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (3 : ℚ)) (m := m + m) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (3 : ℚ)) (m := m + m) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (3 : ℚ)) (m := m + m) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (3 : ℚ)) (m := m + m) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (3 : ℚ)) (m := m + m) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (3 : ℚ)) (m := m + m) (by parley_side)); parley_side)
      _ = 3 ^ m * 3 ^ m * 3 := by parley_subst s9
  -- 11. def:sqrt x := 3
  have r57_1 : (3 : ℤ) ≥ 0 := by parley_arith
  have s11a : Real.sqrt (3 : ℝ) ≥ 0 := by exact (Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := (3 : ℝ)) (by parley_side))
  have s11b : Real.sqrt (3 : ℝ) ^ 2 = 3 := by exact (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := (3 : ℝ)) (by parley_side))
  -- 12. def:sqrt x := 3^k
  have r61_1 : (0 : ℤ) ≤ 3 ^ k.toNat := by parley_order
  have s12a : Real.sqrt (3 ^ k.toNat : ℝ) ≥ 0 := by exact (Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := (3 ^ k.toNat : ℝ)) (by parley_side))
  have s12b : Real.sqrt (3 ^ k.toNat : ℝ) ^ 2 = 3 ^ k.toNat := by exact (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := (3 ^ k.toNat : ℝ)) (by parley_side))
  -- 13. mun:product-nonneg x := √3, y := 3^m, from 6, 11
  have r65_1 : (0 : ℚ) ≤ 3 ^ m := by parley_order
  have s13 : Real.sqrt (3 : ℝ) * 3 ^ m ≥ 0 := by exact (Parley.Items.Stdlib.Numbers.mun_product_nonneg (x := Real.sqrt (3 : ℝ)) (y := (3 ^ m : ℝ)) (by parley_side) (by parley_side))
  -- 14. calculation
  have s14 : Real.sqrt (3 ^ k.toNat : ℝ) ^ 2 = (Real.sqrt (3 : ℝ) * 3 ^ m) ^ 2 := by
    calc Real.sqrt (3 ^ k.toNat : ℝ) ^ 2 = 3 ^ k.toNat := by first | parley_side | parley_line_toNat s12a | parley_line_toNat s12b
      _ = 3 ^ m * 3 ^ m * 3 := by first | parley_side | parley_line_toNat s10
      _ = (Real.sqrt (3 : ℝ) * 3 ^ m) ^ 2 := by linear_combination (norm := parley_norm) (-((3 ^ m) ^ 2)) * s11b
  -- 15. thm:sqrt3-irrational
  have s15 : Irrational (Real.sqrt (3 : ℝ)) := by exact Parley.Proofs.Hammack.Sqrt3Irrational.Sqrt3Irrational.sqrt3_irrational
  -- 16. thm:irrational-product A := √3, B := 3^m, from 6, 15
  have s16 : Irrational (Real.sqrt (3 : ℝ) * 3 ^ m) := by first | exact (Parley.Proofs.Setmm.RationalClosure.IrrationalProduct.irrational_product (A := Real.sqrt (3 : ℝ)) (B := (3 ^ m : ℚ)) (by parley_side) s15) | exact ((Parley.Proofs.Setmm.RationalClosure.IrrationalProduct.irrational_product (A := Real.sqrt (3 : ℝ)) (B := (3 ^ m : ℚ)) (by parley_side) s15)).symm | simpa using (Parley.Proofs.Setmm.RationalClosure.IrrationalProduct.irrational_product (A := Real.sqrt (3 : ℝ)) (B := (3 ^ m : ℚ)) (by parley_side) s15) | exact_mod_cast (Parley.Proofs.Setmm.RationalClosure.IrrationalProduct.irrational_product (A := Real.sqrt (3 : ℝ)) (B := (3 ^ m : ℚ)) (by parley_side) s15) | (have h := (Parley.Proofs.Setmm.RationalClosure.IrrationalProduct.irrational_product (A := Real.sqrt (3 : ℝ)) (B := (3 ^ m : ℚ)) (by parley_side) s15); parley_rat_of_real h) | (have h := (Parley.Proofs.Setmm.RationalClosure.IrrationalProduct.irrational_product (A := Real.sqrt (3 : ℝ)) (B := (3 ^ m : ℚ)) (by parley_side) s15); parley_side)
  -- 17. substitute
  have c1 : Real.sqrt (3 : ℝ) * 3 ^ m = Real.sqrt (3 ^ k.toNat : ℝ) := (((Parley.Items.Stdlib.Numbers.mun_square_equal (x := Real.sqrt (3 ^ k.toNat : ℝ)) (y := Real.sqrt (3 : ℝ) * 3 ^ m) (by parley_side) (by parley_side))).mp s14).symm
  have row1 : Irrational (Real.sqrt (3 ^ k.toNat : ℝ)) := by parley_subst_at c1 s16
  exact row1

end Parley.Proofs.Hammack.SqrtOfOddPowerOfThree.SqrtOfOddPowerOfThree
