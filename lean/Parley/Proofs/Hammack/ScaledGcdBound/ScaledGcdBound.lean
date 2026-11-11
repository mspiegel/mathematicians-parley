module

public import AlgebraTactics
public import OrderTactics
public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Numbers
public import Parley.Proofs.Hammack.DividesProduct.DividesProduct
public import Parley.Proofs.Hammack.ScaledGcdBound.GcdPositive
public import Parley.Proofs.Hammack.ScaledGcdBound.ScaledPairNotBothZero

/-! Written from proofs/hammack/scaled-gcd-bound.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.ScaledGcdBound.ScaledGcdBound

set_option maxHeartbeats 600000 in
theorem scaled_gcd_bound (a : ℤ) (b : ℤ) (c : ℤ) (hH4 : ¬ (a = 0 ∧ b = 0)) (hH5 : c ≠ 0) :
    c * (Int.gcd a b : ℤ) ≤ (Int.gcd (c * a) (c * b) : ℤ) := by
  -- 1. thm:gcd-positive x := a, y := b, from H4
  have s1 : 0 < (Int.gcd a b : ℤ) := by exact (Parley.Proofs.Hammack.ScaledGcdBound.GcdPositive.gcd_positive (x := a) (y := b) hH4)
  -- 2. mun:gcd-integer
  have s2 : (Int.gcd a b : ℤ) ∣ a := by exact (Parley.Items.Stdlib.Divisibility.mun_gcd_integer_2 (a := a) (b := b))
  -- 3. mun:gcd-integer
  have s3 : (Int.gcd a b : ℤ) ∣ b := by exact (Parley.Items.Stdlib.Divisibility.mun_gcd_integer_3 (a := a) (b := b))
  -- 4. thm:scaled-pair-not-both-zero x := a, y := b, from H4, H5
  have s4 : ¬ (c * a = 0 ∧ c * b = 0) := by exact (Parley.Proofs.Hammack.ScaledGcdBound.ScaledPairNotBothZero.scaled_pair_not_both_zero (x := a) (y := b) (c := c) hH4 hH5)
  -- 5. thm:gcd-positive x := c·a, y := c·b, from 4
  have s5 : 0 < (Int.gcd (c * a) (c * b) : ℤ) := by exact (Parley.Proofs.Hammack.ScaledGcdBound.GcdPositive.gcd_positive (x := c * a) (y := c * b) s4)
  -- 6. mun:divides-self n := c
  have s6 : c ∣ c := by exact (Parley.Items.Stdlib.Divisibility.mun_divides_self (n := c))
  -- 7. thm:divides-product a := c, b := c, c := gcd(a, b), d := a, from 2, 6
  have s7 : c * (Int.gcd a b : ℤ) ∣ c * a := by exact (Parley.Proofs.Hammack.DividesProduct.DividesProduct.divides_product (a := c) (b := c) (c := (Int.gcd a b : ℤ)) (d := a) s6 s2)
  -- 8. thm:divides-product a := c, b := c, c := gcd(a, b), d := b, from 3, 6
  have s8 : c * (Int.gcd a b : ℤ) ∣ c * b := by exact (Parley.Proofs.Hammack.DividesProduct.DividesProduct.divides_product (a := c) (b := c) (c := (Int.gcd a b : ℤ)) (d := b) s6 s3)
  -- 9. thm:divides-gcd d := c·gcd(a, b), a := c·a, b := c·b, from 7, 8
  have s9 : c * (Int.gcd a b : ℤ) ∣ (Int.gcd (c * a) (c * b) : ℤ) := by exact (Parley.Items.Stdlib.Divisibility.thm_divides_gcd (d := c * (Int.gcd a b : ℤ)) (a := c * a) (b := c * b) s7 s8)
  -- 10. mun:nonneg-or-neg x := c
  have s10 : c ≥ 0 ∨ c < 0 := by exact (Parley.Items.Stdlib.Numbers.mun_nonneg_or_neg (x := c))
  -- 11. cases, from 10
  rcases s10 with hC1 | hC2
  · skip
    -- 11.1. inequalities, from C1, H5
    have s11_1 : 0 < c := by parley_order
    -- 11.2. mun:pos-int-nat m := c, from 11.1
    have s11_2 : 0 < c := by exact (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := c) s11_1)
    -- 11.3. mun:nat-closure a := c, b := gcd(a, b), from 1, 11.2
    have s11_3 : 0 < c * (Int.gcd a b : ℤ) := by exact (Parley.Items.Stdlib.Numbers.mun_nat_closure_2 (a := c) (by parley_side) (b := (Int.gcd a b : ℤ)) (by parley_side))
    -- 11.4. mun:divides-le e := c·gcd(a, b), m := gcd(c·a, c·b), from 5, 9, 11.3
    exact (Parley.Items.Stdlib.Divisibility.mun_divides_le (e := c * (Int.gcd a b : ℤ)) (by parley_side) (m := (Int.gcd (c * a) (c * b) : ℤ)) (by parley_side) s9)
  · skip
    -- 11.5. inequalities
    have s11_5 : 0 < -c := by parley_order
    -- 11.6. inequalities, from 1
    have s11_6 : 0 < (Int.gcd a b : ℤ) := by parley_order
    -- 11.7. mun:product-positive x := −c, y := gcd(a, b), from 11.5, 11.6
    have s11_7 : 0 < -c * (Int.gcd a b : ℤ) := by exact (Parley.Items.Stdlib.Numbers.mun_product_positive (x := -c) (y := (Int.gcd a b : ℤ)) (by parley_side) (by parley_side))
    -- 11.8. substitute
    have s11_8 : 0 < -(c * (Int.gcd a b : ℤ)) := by
      have c1 : -c * (Int.gcd a b : ℤ) = -(c * (Int.gcd a b : ℤ)) := by parley_ring
      have row1 : 0 < -(c * (Int.gcd a b : ℤ)) := by (have h := Eq.subst (motive := (fun t : ℤ => 0 < t)) c1 s11_7; push_cast at h ⊢; all_goals exact_mod_cast h)
      exact row1
    -- 11.9. inequalities
    have s11_9 : c * (Int.gcd a b : ℤ) < 0 := by parley_order
    -- 11.10. inequalities, from 5, 11.9
    have s11_10 : c * (Int.gcd a b : ℤ) < (Int.gcd (c * a) (c * b) : ℤ) := by parley_order
    -- 11.11. inequalities
    parley_order

end Parley.Proofs.Hammack.ScaledGcdBound.ScaledGcdBound
