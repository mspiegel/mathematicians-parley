module

public import AlgebraTactics
public import OrderTactics
public import Tactics
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Numbers
public import Parley.Proofs.Hammack.GcdIntegerNatural.GcdIntegerNatural

/-! Written from proofs/hammack/odd-and-quartic-coprime.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.OddAndQuarticCoprime.OddAndQuarticCoprime

theorem odd_and_quartic_coprime (n : ℤ) :
    (Int.gcd (2 * n + 1) (4 * n ^ 2 + 1) : ℤ) = 1 := by
  -- 1. mun:square-nonneg x := n
  have s1 : n ^ 2 ≥ 0 := by exact (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := n))
  -- 2. inequalities
  have s2 : 4 * n ^ 2 + 1 ≥ 1 := by parley_order
  -- 3. mun:pos-int-nat m := 4n² + 1
  have r26_1 : 0 < 4 * n ^ 2 + 1 := by parley_order
  have s3 : 0 < 4 * n ^ 2 + 1 := by exact (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := 4 * n ^ 2 + 1) r26_1)
  -- 4. thm:gcd-integer-natural a := 2n + 1, b := 4n² + 1, from 3
  have s4a : 0 < (Int.gcd (2 * n + 1) (4 * n ^ 2 + 1) : ℤ) := by exact (Parley.Proofs.Hammack.GcdIntegerNatural.GcdIntegerNatural.gcd_integer_natural (a := 2 * n + 1) (b := 4 * n ^ 2 + 1) s3).1
  have s4b : (Int.gcd (2 * n + 1) (4 * n ^ 2 + 1) : ℤ) ∣ 2 * n + 1 := by exact (Parley.Proofs.Hammack.GcdIntegerNatural.GcdIntegerNatural.gcd_integer_natural (a := 2 * n + 1) (b := 4 * n ^ 2 + 1) s3).2.1
  have s4c : (Int.gcd (2 * n + 1) (4 * n ^ 2 + 1) : ℤ) ∣ 4 * n ^ 2 + 1 := by exact (Parley.Proofs.Hammack.GcdIntegerNatural.GcdIntegerNatural.gcd_integer_natural (a := 2 * n + 1) (b := 4 * n ^ 2 + 1) s3).2.2
  -- 5. mun:divides-multiple e := gcd(2n + 1, 4n² + 1), a := 2n + 1, x := 2n − 1, from 4
  have s5 : (Int.gcd (2 * n + 1) (4 * n ^ 2 + 1) : ℤ) ∣ (2 * n + 1) * (2 * n - 1) := by exact (Parley.Items.Stdlib.Divisibility.mun_divides_multiple (e := (Int.gcd (2 * n + 1) (4 * n ^ 2 + 1) : ℤ)) (a := 2 * n + 1) (x := 2 * n - 1) s4b)
  -- 6. mun:divides-difference d := gcd(2n + 1, 4n² + 1), a := 4n² + 1, b := (2n + 1)·(2n − 1), from 4, 5
  have s6 : (Int.gcd (2 * n + 1) (4 * n ^ 2 + 1) : ℤ) ∣ 4 * n ^ 2 + 1 - (2 * n + 1) * (2 * n - 1) := by exact (Parley.Items.Stdlib.Divisibility.mun_divides_difference (d := (Int.gcd (2 * n + 1) (4 * n ^ 2 + 1) : ℤ)) (a := 4 * n ^ 2 + 1) (b := (2 * n + 1) * (2 * n - 1)) s4c s5)
  -- 7. substitute
  have s7 : (Int.gcd (2 * n + 1) (4 * n ^ 2 + 1) : ℤ) ∣ (2 : ℤ) := by
    have c1 : 4 * n ^ 2 + 1 - (2 * n + 1) * (2 * n - 1) = 2 := by parley_ring
    have row1 : (Int.gcd (2 * n + 1) (4 * n ^ 2 + 1) : ℤ) ∣ (2 : ℤ) := by (have h := Eq.subst (motive := (fun t : ℤ => (Int.gcd (2 * n + 1) (4 * n ^ 2 + 1) : ℤ) ∣ t)) c1 s6; push_cast at h ⊢; all_goals exact_mod_cast h)
    exact row1
  -- 8. mun:divides-combination e := gcd(2n + 1, 4n² + 1), a := 2n + 1, b := 2, x := 1, y := −n, from 4, 7
  have s8 : (Int.gcd (2 * n + 1) (4 * n ^ 2 + 1) : ℤ) ∣ (2 * n + 1) * 1 + 2 * -n := by exact (Parley.Items.Stdlib.Divisibility.mun_divides_combination (e := (Int.gcd (2 * n + 1) (4 * n ^ 2 + 1) : ℤ)) (a := 2 * n + 1) (b := (2 : ℤ)) (x := (1 : ℤ)) (y := -n) s4b s7)
  -- 9. substitute
  have s9 : (Int.gcd (2 * n + 1) (4 * n ^ 2 + 1) : ℤ) ∣ (1 : ℤ) := by
    have c1 : (2 * n + 1) * 1 + 2 * -n = 1 := by parley_ring
    have row1 : (Int.gcd (2 * n + 1) (4 * n ^ 2 + 1) : ℤ) ∣ (1 : ℤ) := by (have h := Eq.subst (motive := (fun t : ℤ => (Int.gcd (2 * n + 1) (4 * n ^ 2 + 1) : ℤ) ∣ t)) c1 s8; push_cast at h ⊢; all_goals exact_mod_cast h)
    exact row1
  -- 10. mun:divides-one d := gcd(2n + 1, 4n² + 1), from 4, 9
  exact (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := (Int.gcd (2 * n + 1) (4 * n ^ 2 + 1) : ℤ)) s4a s9)

end Parley.Proofs.Hammack.OddAndQuarticCoprime.OddAndQuarticCoprime
