module

public import ArithTactics
public import PowerTactics
public import SubstTactics
public import Tactics
public import Batteries.Tactic.Init
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Reasoning

/-! Written from proofs/hammack/scaled-gcd-bound.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.ScaledGcdBound.GcdPositive

set_option maxHeartbeats 400000 in
theorem gcd_positive (x : ℤ) (y : ℤ) (hH3 : ¬ (x = 0 ∧ y = 0)) :
    0 < (Int.gcd x y : ℤ) := by
  -- 1. mun:gcd-integer
  have s1 : (Int.gcd x y : ℤ) ∣ x := by first | exact (Parley.Items.Stdlib.Divisibility.mun_gcd_integer_2 (a := x) (b := y)) | exact ((Parley.Items.Stdlib.Divisibility.mun_gcd_integer_2 (a := x) (b := y))).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_gcd_integer_2 (a := x) (b := y)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_gcd_integer_2 (a := x) (b := y)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_gcd_integer_2 (a := x) (b := y)); parley_side)
  -- 2. mun:gcd-integer
  have s2 : (Int.gcd x y : ℤ) ∣ y := by first | exact (Parley.Items.Stdlib.Divisibility.mun_gcd_integer_3 (a := x) (b := y)) | exact ((Parley.Items.Stdlib.Divisibility.mun_gcd_integer_3 (a := x) (b := y))).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_gcd_integer_3 (a := x) (b := y)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_gcd_integer_3 (a := x) (b := y)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_gcd_integer_3 (a := x) (b := y)); parley_side)
  -- 3. contradiction
  have s3 : (Int.gcd x y : ℤ) ≠ 0 := by
    by_contra hc_hS
    have hS : (Int.gcd x y : ℤ) = 0 := by parley_suppose hc_hS
    -- 3.1. substitute gcd(x, y) = 0 (S) into line 1
    have s3_1 : (0 : ℤ) ∣ x := by first | parley_subst_at hS s1 | (have e_nat : Int.gcd x y = 0 := by exact_mod_cast hS; parley_subst_at e_nat s1)
    -- 3.2. mun:zero-divides n := x
    have s3_2 : (0 : ℤ) ∣ x ↔ x = 0 := by first | exact (Parley.Items.Stdlib.Divisibility.mun_zero_divides (n := x)) | exact ((Parley.Items.Stdlib.Divisibility.mun_zero_divides (n := x))).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_zero_divides (n := x)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_zero_divides (n := x)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_zero_divides (n := x)); parley_side)
    -- 3.3. mun:iff-from-left P := 0 divides x, Q := x = 0, from 3.1, 3.2
    have s3_3 : x = 0 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Reasoning.mun_iff_from_left (P := (0 : ℤ) ∣ x) (Q := x = 0) s3_2 s3_1) | (have h := (Parley.Items.Stdlib.Reasoning.mun_iff_from_left (P := (0 : ℤ) ∣ x) (Q := x = 0) s3_2 s3_1); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Reasoning.mun_iff_from_left (P := (0 : ℤ) ∣ x) (Q := x = 0) s3_2 s3_1); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_iff_from_left (P := (0 : ℤ) ∣ x) (Q := x = 0) s3_2 s3_1) | exact_mod_cast ((Parley.Items.Stdlib.Reasoning.mun_iff_from_left (P := (0 : ℤ) ∣ x) (Q := x = 0) s3_2 s3_1)).symm | (have h := (Parley.Items.Stdlib.Reasoning.mun_iff_from_left (P := (0 : ℤ) ∣ x) (Q := x = 0) s3_2 s3_1); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Reasoning.mun_iff_from_left (P := (0 : ℤ) ∣ x) (Q := x = 0) s3_2 s3_1); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Reasoning.mun_iff_from_left (P := (0 : ℤ) ∣ x) (Q := x = 0) s3_2 s3_1); parley_int_power h) | (have h := (Parley.Items.Stdlib.Reasoning.mun_iff_from_left (P := (0 : ℤ) ∣ x) (Q := x = 0) s3_2 s3_1); parley_side)
    -- 3.4. substitute gcd(x, y) = 0 (S) into line 2
    have s3_4 : (0 : ℤ) ∣ y := by first | parley_subst_at hS s2 | (have e_nat : Int.gcd x y = 0 := by exact_mod_cast hS; parley_subst_at e_nat s2)
    -- 3.5. mun:zero-divides n := y
    have s3_5 : (0 : ℤ) ∣ y ↔ y = 0 := by first | exact (Parley.Items.Stdlib.Divisibility.mun_zero_divides (n := y)) | exact ((Parley.Items.Stdlib.Divisibility.mun_zero_divides (n := y))).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_zero_divides (n := y)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_zero_divides (n := y)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_zero_divides (n := y)); parley_side)
    -- 3.6. mun:iff-from-left P := 0 divides y, Q := y = 0, from 3.4, 3.5
    have s3_6 : y = 0 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Reasoning.mun_iff_from_left (P := (0 : ℤ) ∣ y) (Q := y = 0) s3_5 s3_4) | (have h := (Parley.Items.Stdlib.Reasoning.mun_iff_from_left (P := (0 : ℤ) ∣ y) (Q := y = 0) s3_5 s3_4); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Reasoning.mun_iff_from_left (P := (0 : ℤ) ∣ y) (Q := y = 0) s3_5 s3_4); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_iff_from_left (P := (0 : ℤ) ∣ y) (Q := y = 0) s3_5 s3_4) | exact_mod_cast ((Parley.Items.Stdlib.Reasoning.mun_iff_from_left (P := (0 : ℤ) ∣ y) (Q := y = 0) s3_5 s3_4)).symm | (have h := (Parley.Items.Stdlib.Reasoning.mun_iff_from_left (P := (0 : ℤ) ∣ y) (Q := y = 0) s3_5 s3_4); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Reasoning.mun_iff_from_left (P := (0 : ℤ) ∣ y) (Q := y = 0) s3_5 s3_4); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Reasoning.mun_iff_from_left (P := (0 : ℤ) ∣ y) (Q := y = 0) s3_5 s3_4); parley_int_power h) | (have h := (Parley.Items.Stdlib.Reasoning.mun_iff_from_left (P := (0 : ℤ) ∣ y) (Q := y = 0) s3_5 s3_4); parley_side)
    -- 3.7. join 3.3, 3.6
    have s3_7 : x = 0 ∧ y = 0 := by parley_side
    all_goals parley_side
  -- 4. mun:nat0-nonzero m := gcd(x, y), from 3
  have s4 : 0 < (Int.gcd x y : ℤ) := by first | exact (Parley.Items.Stdlib.Numbers.mun_nat0_nonzero (m := (Int.gcd x y : ℤ)) (by parley_side) s3) | exact ((Parley.Items.Stdlib.Numbers.mun_nat0_nonzero (m := (Int.gcd x y : ℤ)) (by parley_side) s3)).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_nat0_nonzero (m := (Int.gcd x y : ℤ)) (by parley_side) s3) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_nat0_nonzero (m := (Int.gcd x y : ℤ)) (by parley_side) s3) | (have h := (Parley.Items.Stdlib.Numbers.mun_nat0_nonzero (m := (Int.gcd x y : ℤ)) (by parley_side) s3); parley_side)
  all_goals exact s4

end Parley.Proofs.Hammack.ScaledGcdBound.GcdPositive
