module

public import NormTactics
public import SubstTactics
public import Tactics
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Divisibility

/-! Written from proofs/wiedijk/pythagorean-triples.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.PythagoreanTriples.LegHypotenuseCoprime

set_option maxHeartbeats 400000 in
theorem leg_hypotenuse_coprime (a : ℤ) (hH1 : 0 < a) (b : ℤ) (hH2 : 0 < b) (c : ℤ) (hH3 : 0 < c) (hH4 : a ^ 2 + b ^ 2 = c ^ 2) (hH5 : (Int.gcd a b : ℤ) = 1) :
    (Int.gcd b c : ℤ) = 1 := by
  -- 1. def:gcd a := b, b := c
  have s1a : 0 < (Int.gcd b c : ℤ) := by exact (Parley.Items.Stdlib.Divisibility.def_gcd_1 (a := b) (by parley_side) (b := c) (by parley_side))
  have s1b : (Int.gcd b c : ℤ) ∣ b := by exact (Parley.Items.Stdlib.Divisibility.def_gcd_2 (a := b) (by parley_side) (b := c) (by parley_side))
  have s1c : (Int.gcd b c : ℤ) ∣ c := by exact (Parley.Items.Stdlib.Divisibility.def_gcd_3 (a := b) (by parley_side) (b := c) (by parley_side))
  -- 2. mun:divides-combination e := gcd(b, c), a := c, x := c, y := −b, from 1
  have s2 : (Int.gcd b c : ℤ) ∣ c * c + b * -b := by exact (Parley.Items.Stdlib.Divisibility.mun_divides_combination (e := (Int.gcd b c : ℤ)) (a := c) (b := b) (x := c) (y := -b) s1c s1b)
  -- 3. substitute
  have s3 : (Int.gcd b c : ℤ) ∣ a * a := by
    have c1 : c * c + b * -b = a * a := by linear_combination (norm := parley_norm) (-1) * hH4
    have row1 : (Int.gcd b c : ℤ) ∣ a * a := by parley_subst_at c1 s2
    exact row1
  -- 4. def:gcd a := gcd(b, c), b := a, from 1
  have s4a : 0 < (Int.gcd (Int.gcd b c : ℤ) a : ℤ) := by exact (Parley.Items.Stdlib.Divisibility.def_gcd_1 (a := (Int.gcd b c : ℤ)) (by parley_side) (b := a) (by parley_side))
  have s4b : (Int.gcd (Int.gcd b c : ℤ) a : ℤ) ∣ (Int.gcd b c : ℤ) := by exact (Parley.Items.Stdlib.Divisibility.def_gcd_2 (a := (Int.gcd b c : ℤ)) (by parley_side) (b := a) (by parley_side))
  have s4c : (Int.gcd (Int.gcd b c : ℤ) a : ℤ) ∣ a := by exact (Parley.Items.Stdlib.Divisibility.def_gcd_3 (a := (Int.gcd b c : ℤ)) (by parley_side) (b := a) (by parley_side))
  -- 5. mun:divides-transitive d := gcd(gcd(b, c), a), e := gcd(b, c), n := b, from 1, 4
  have s5 : (Int.gcd (Int.gcd b c : ℤ) a : ℤ) ∣ b := by exact (Parley.Items.Stdlib.Divisibility.mun_divides_transitive (d := (Int.gcd (Int.gcd b c : ℤ) a : ℤ)) (e := (Int.gcd b c : ℤ)) (n := b) s4b s1b)
  -- 6. thm:divides-gcd d := gcd(gcd(b, c), a), from 4, 5
  have s6 : (Int.gcd (Int.gcd b c : ℤ) a : ℤ) ∣ (Int.gcd a b : ℤ) := by exact (Parley.Items.Stdlib.Divisibility.thm_divides_gcd (d := (Int.gcd (Int.gcd b c : ℤ) a : ℤ)) (a := a) (b := b) s4c s5)
  -- 7. substitute gcd(a, b) = 1 (H5) into line 6
  have s7 : (Int.gcd (Int.gcd b c : ℤ) a : ℤ) ∣ (1 : ℤ) := by first | parley_subst_at hH5 s6 | (have e_nat : Int.gcd a b = 1 := by exact_mod_cast hH5; parley_subst_at e_nat s6)
  -- 8. calculation
  have s8 : (Int.gcd a (Int.gcd b c : ℤ) : ℤ) = 1 := by
    calc (Int.gcd a (Int.gcd b c : ℤ) : ℤ) = (Int.gcd (Int.gcd b c : ℤ) a : ℤ) := by exact (Parley.Items.Stdlib.Divisibility.mun_gcd_commutes (a := a) (b := (Int.gcd b c : ℤ)))
      _ = 1 := by exact (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := (Int.gcd (Int.gcd b c : ℤ) a : ℤ)) (by parley_side) s7)
  -- 9. mun:divides-self n := gcd(b, c)
  have s9 : (Int.gcd b c : ℤ) ∣ (Int.gcd b c : ℤ) := by exact (Parley.Items.Stdlib.Divisibility.mun_divides_self (n := (Int.gcd b c : ℤ)))
  -- 10. thm:divides-gcd d := gcd(b, c), a := a·a, b := gcd(b, c), from 3, 9
  have s10 : (Int.gcd b c : ℤ) ∣ (Int.gcd (a * a) (Int.gcd b c : ℤ) : ℤ) := by exact (Parley.Items.Stdlib.Divisibility.thm_divides_gcd (d := (Int.gcd b c : ℤ)) (a := a * a) (b := (Int.gcd b c : ℤ)) s3 s9)
  -- 11. substitute
  have s11 : (Int.gcd b c : ℤ) ∣ (1 : ℤ) := by
    have c1 : (Int.gcd (a * a) (Int.gcd b c : ℤ) : ℤ) = 1 := by exact (Parley.Items.Stdlib.Divisibility.mun_coprime_product (x := a) (y := a) (n := (Int.gcd b c : ℤ)) (by parley_side) s8 s8)
    have row1 : (Int.gcd b c : ℤ) ∣ (1 : ℤ) := by parley_subst_at c1 s10
    exact row1
  -- 12. mun:divides-one d := gcd(b, c), from 1, 11
  exact (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := (Int.gcd b c : ℤ)) (by parley_side) s11)

end Parley.Proofs.Wiedijk.PythagoreanTriples.LegHypotenuseCoprime
