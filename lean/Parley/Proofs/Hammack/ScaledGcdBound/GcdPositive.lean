module

public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Cast.Order.Ring
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Reasoning

/-! Written from proofs/hammack/scaled-gcd-bound.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.ScaledGcdBound.GcdPositive

theorem gcd_positive (x : ℤ) (y : ℤ) (hH3 : ¬ (x = 0 ∧ y = 0)) :
    0 < (Int.gcd x y : ℤ) := by
  -- 1. mun:gcd-integer
  have s1 : (Int.gcd x y : ℤ) ∣ x := by exact (Parley.Items.Stdlib.Divisibility.mun_gcd_integer_2 (a := x) (b := y))
  -- 2. mun:gcd-integer
  have s2 : (Int.gcd x y : ℤ) ∣ y := by exact (Parley.Items.Stdlib.Divisibility.mun_gcd_integer_3 (a := x) (b := y))
  -- 3. contradiction
  have s3 : (Int.gcd x y : ℤ) ≠ 0 := by
    intro hS
    -- 3.1. substitute gcd(x, y) = 0 (S) into line 1
    have s3_1 : (0 : ℤ) ∣ x := by (have h := Eq.subst (motive := (fun t : ℤ => t ∣ x)) hS s1; push_cast at h ⊢; all_goals exact_mod_cast h)
    -- 3.2. mun:zero-divides n := x
    have s3_2 : (0 : ℤ) ∣ x ↔ x = 0 := by exact (Parley.Items.Stdlib.Divisibility.mun_zero_divides (n := x))
    -- 3.3. mun:iff-from-left P := 0 divides x, Q := x = 0, from 3.1, 3.2
    have s3_3 : x = 0 := by exact (Parley.Items.Stdlib.Reasoning.mun_iff_from_left (P := (0 : ℤ) ∣ x) (Q := x = 0) s3_2 s3_1)
    -- 3.4. substitute gcd(x, y) = 0 (S) into line 2
    have s3_4 : (0 : ℤ) ∣ y := by (have h := Eq.subst (motive := (fun t : ℤ => t ∣ y)) hS s2; push_cast at h ⊢; all_goals exact_mod_cast h)
    -- 3.5. mun:zero-divides n := y
    have s3_5 : (0 : ℤ) ∣ y ↔ y = 0 := by exact (Parley.Items.Stdlib.Divisibility.mun_zero_divides (n := y))
    -- 3.6. mun:iff-from-left P := 0 divides y, Q := y = 0, from 3.4, 3.5
    have s3_6 : y = 0 := by exact (Parley.Items.Stdlib.Reasoning.mun_iff_from_left (P := (0 : ℤ) ∣ y) (Q := y = 0) s3_5 s3_4)
    -- 3.7. join 3.3, 3.6
    have s3_7 : x = 0 ∧ y = 0 := ⟨s3_3, s3_6⟩
    exact hH3 s3_7
  -- 4. mun:nat0-nonzero m := gcd(x, y), from 3
  exact (Parley.Items.Stdlib.Numbers.mun_nat0_nonzero (m := (Int.gcd x y : ℤ)) (Nat.cast_nonneg _) s3)

end Parley.Proofs.Hammack.ScaledGcdBound.GcdPositive
