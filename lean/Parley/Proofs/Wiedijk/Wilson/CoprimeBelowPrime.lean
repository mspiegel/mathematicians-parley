module

public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Divisibility

/-! Written from proofs/wiedijk/wilson.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.Wilson.CoprimeBelowPrime

theorem coprime_below_prime (p : ℤ) (hH1 : 0 < p) (hH2 : Nat.Prime p.toNat) (a : ℤ) (hH3 : 0 < a) (hH4 : a < p) :
    (Int.gcd a p : ℤ) = 1 := by
  -- 1. mun:below-not-divisible n := p, x := a, from H4
  have s1 : ¬ p ∣ a := by exact (Parley.Items.Stdlib.Divisibility.mun_below_not_divisible (n := p) hH1 (x := a) hH3 hH4)
  -- 2. calculation
  calc (Int.gcd a p : ℤ) = (Int.gcd p a : ℤ) := by exact (Parley.Items.Stdlib.Divisibility.mun_gcd_commutes (a := a) (b := p))
    _ = 1 := by exact (Parley.Items.Stdlib.Divisibility.mun_prime_coprime (p := p) hH1 hH2 (a := a) s1)

end Parley.Proofs.Wiedijk.Wilson.CoprimeBelowPrime
