module

public import AlgebraTactics
public import Tactics
public import Batteries.Tactic.Init
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Divisibility
public import Parley.Proofs.Hammack.Sqrt3Irrational.ThreePrime

/-! Written from proofs/hammack/sqrt3-irrational.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.Sqrt3Irrational.ThreeDividesSquare

theorem three_divides_square (n : ℤ) (hH2 : (3 : ℤ) ∣ n ^ 2) :
    (3 : ℤ) ∣ n := by
  -- the theorem. contradiction
  by_contra hS
  -- 1. thm:three-prime
  have s1 : Nat.Prime (3 : ℤ).toNat := by exact Parley.Proofs.Hammack.Sqrt3Irrational.ThreePrime.three_prime
  -- 2. calculation
  have s2 : (Int.gcd n (3 : ℤ) : ℤ) = 1 := by
    calc (Int.gcd n (3 : ℤ) : ℤ) = (Int.gcd (3 : ℤ) n : ℤ) := by exact (Parley.Items.Stdlib.Divisibility.mun_gcd_commutes (a := n) (b := (3 : ℤ)))
      _ = 1 := by exact (Parley.Items.Stdlib.Divisibility.mun_prime_coprime (p := (3 : ℤ)) (by parley_side) s1 (a := n) hS)
  -- 3. substitute
  have s3 : (3 : ℤ) ∣ n * n := by
    have c1 : n ^ 2 = n * n := by parley_ring
    have row1 : (3 : ℤ) ∣ n * n := by (have h := Eq.subst (motive := (fun t : ℤ => (3 : ℤ) ∣ t)) c1 hH2; push_cast at h ⊢; all_goals exact_mod_cast h)
    exact row1
  -- 4. thm:coprime-divides x := n, c := n, n := 3, from 2, 3
  have s4 : (3 : ℤ) ∣ n := by exact (Parley.Items.Stdlib.Divisibility.thm_coprime_divides (x := n) (c := n) (n := (3 : ℤ)) (by parley_side) s3 s2)
  exact hS s4

end Parley.Proofs.Hammack.Sqrt3Irrational.ThreeDividesSquare
