module

public import OrderTactics
public import RealTactics
public import Tactics
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
  have s1 : (s - r) / 2 > 0 := by parley_order
  -- 2. thm:sqrt2-irrational
  have s2 : Irrational (Real.sqrt (2 : ℝ)) := by first | exact Parley.Proofs.Wiedijk.Sqrt2Irrational.Sqrt2Irrational.sqrt2_irrational | exact (Parley.Proofs.Wiedijk.Sqrt2Irrational.Sqrt2Irrational.sqrt2_irrational).symm | simpa using Parley.Proofs.Wiedijk.Sqrt2Irrational.Sqrt2Irrational.sqrt2_irrational | exact_mod_cast Parley.Proofs.Wiedijk.Sqrt2Irrational.Sqrt2Irrational.sqrt2_irrational | (have h := Parley.Proofs.Wiedijk.Sqrt2Irrational.Sqrt2Irrational.sqrt2_irrational; parley_side)
  -- 3. thm:irrational-product A := √2, B := (s − r)/2, from 2
  have r26_1 : (s - r) / 2 ≠ 0 := by parley_side
  have s3 : Irrational (Real.sqrt (2 : ℝ) * (((s : ℝ) - (r : ℝ)) / 2)) := by first | exact (Parley.Proofs.Setmm.RationalClosure.IrrationalProduct.irrational_product (A := Real.sqrt (2 : ℝ)) (B := (s - r) / 2) (by parley_side) s2) | exact ((Parley.Proofs.Setmm.RationalClosure.IrrationalProduct.irrational_product (A := Real.sqrt (2 : ℝ)) (B := (s - r) / 2) (by parley_side) s2)).symm | simpa using (Parley.Proofs.Setmm.RationalClosure.IrrationalProduct.irrational_product (A := Real.sqrt (2 : ℝ)) (B := (s - r) / 2) (by parley_side) s2) | exact_mod_cast (Parley.Proofs.Setmm.RationalClosure.IrrationalProduct.irrational_product (A := Real.sqrt (2 : ℝ)) (B := (s - r) / 2) (by parley_side) s2) | (have h := (Parley.Proofs.Setmm.RationalClosure.IrrationalProduct.irrational_product (A := Real.sqrt (2 : ℝ)) (B := (s - r) / 2) (by parley_side) s2); parley_side)
  -- 4. thm:irrational-sum A := √2·((s − r)/2), B := r, from 3
  have s4 : Irrational (Real.sqrt (2 : ℝ) * (((s : ℝ) - (r : ℝ)) / 2) + (r : ℝ)) := by first | exact (Parley.Proofs.Setmm.RationalClosure.IrrationalSum.irrational_sum (A := Real.sqrt (2 : ℝ) * (((s : ℝ) - (r : ℝ)) / 2)) (B := r) s3) | exact ((Parley.Proofs.Setmm.RationalClosure.IrrationalSum.irrational_sum (A := Real.sqrt (2 : ℝ) * (((s : ℝ) - (r : ℝ)) / 2)) (B := r) s3)).symm | simpa using (Parley.Proofs.Setmm.RationalClosure.IrrationalSum.irrational_sum (A := Real.sqrt (2 : ℝ) * (((s : ℝ) - (r : ℝ)) / 2)) (B := r) s3) | exact_mod_cast (Parley.Proofs.Setmm.RationalClosure.IrrationalSum.irrational_sum (A := Real.sqrt (2 : ℝ) * (((s : ℝ) - (r : ℝ)) / 2)) (B := r) s3) | (have h := (Parley.Proofs.Setmm.RationalClosure.IrrationalSum.irrational_sum (A := Real.sqrt (2 : ℝ) * (((s : ℝ) - (r : ℝ)) / 2)) (B := r) s3); parley_side)
  -- 5. real arithmetic
  have s5 : 0 < Real.sqrt (2 : ℝ) := by parley_real
  -- 6. real arithmetic
  have s6 : Real.sqrt (2 : ℝ) < 2 := by parley_real
  -- 7. mun:product-positive x := √2, y := (s − r)/2, from 1, 5
  have s7 : Real.sqrt (2 : ℝ) * (((s : ℝ) - (r : ℝ)) / 2) > 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_product_positive (x := Real.sqrt (2 : ℝ)) (y := ((s : ℝ) - (r : ℝ)) / 2) (by parley_side) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_product_positive (x := Real.sqrt (2 : ℝ)) (y := ((s : ℝ) - (r : ℝ)) / 2) (by parley_side) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_product_positive (x := Real.sqrt (2 : ℝ)) (y := ((s : ℝ) - (r : ℝ)) / 2) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_product_positive (x := Real.sqrt (2 : ℝ)) (y := ((s : ℝ) - (r : ℝ)) / 2) (by parley_side) (by parley_side)); parley_side)
  -- 8. mun:less-scaled x := √2, y := 2, c := (s − r)/2, from 1, 6
  have s8 : ((s : ℝ) - (r : ℝ)) / 2 * Real.sqrt (2 : ℝ) < ((s : ℝ) - (r : ℝ)) / 2 * 2 := by first | linarith [((Parley.Items.Stdlib.Numbers.mun_less_scaled (x := Real.sqrt (2 : ℝ)) (y := (2 : ℝ)) (c := ((s : ℝ) - (r : ℝ)) / 2) (by parley_side))).mp (by parley_side)] | (have h := ((Parley.Items.Stdlib.Numbers.mun_less_scaled (x := Real.sqrt (2 : ℝ)) (y := (2 : ℝ)) (c := ((s : ℝ) - (r : ℝ)) / 2) (by parley_side))).mp (by parley_side); push_cast at h; linarith) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_less_scaled (x := Real.sqrt (2 : ℝ)) (y := (2 : ℝ)) (c := ((s : ℝ) - (r : ℝ)) / 2) (by parley_side))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_less_scaled (x := Real.sqrt (2 : ℝ)) (y := (2 : ℝ)) (c := ((s : ℝ) - (r : ℝ)) / 2) (by parley_side))).mp (by parley_side); parley_side)
  -- 9. inequalities
  have s9 : (r : ℝ) < Real.sqrt (2 : ℝ) * (((s : ℝ) - (r : ℝ)) / 2) + (r : ℝ) := by parley_order
  -- 10. inequalities
  have s10 : Real.sqrt (2 : ℝ) * (((s : ℝ) - (r : ℝ)) / 2) + (r : ℝ) < (s : ℝ) := by parley_order
  -- 11. exhibit, from 4, 9, 10
  have s11 : ∃ u : ℝ, (Irrational u ∧ (r : ℝ) < u) ∧ u < (s : ℝ) := ⟨Real.sqrt (2 : ℝ) * (((s : ℝ) - (r : ℝ)) / 2) + (r : ℝ), ⟨⟨by parley_side, by parley_side⟩, by parley_side⟩⟩
  all_goals exact s11

end Parley.Proofs.Hammack.IrrationalBetweenRationalsByHalfRootTwo.IrrationalBetweenRationals
