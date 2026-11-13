module

public import AlgebraTactics
public import Counting
public import FactorialTactics
public import Tactics
public import Batteries.Tactic.Init
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Divisibility

/-! Written from proofs/wiedijk/infinitely-many-primes.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.InfinitelyManyPrimes.PrimeAbove

theorem prime_above (n : ℤ) (hH1 : 0 < n) :
    (∃ p : ℤ, 0 < p ∧ (Nat.Prime p.toNat ∧ p > n)) := by
  -- 1. mun:factorial-nat
  have s1 : 0 < (LeanBridges.Counting.factorial n : ℤ) := by exact (Parley.Items.Stdlib.Counting.mun_factorial_nat (n := n) (le_of_lt hH1))
  -- 2. inequalities, from 1
  have s2 : (LeanBridges.Counting.factorial n : ℤ) + 1 > 1 := by linarith only [s1]
  -- 3. obtain p: thm:prime-factor m := n! + 1, from 2
  obtain ⟨p, s3a, ⟨s3b, s3c⟩⟩ := (Parley.Items.Stdlib.Divisibility.thm_prime_factor (m := (LeanBridges.Counting.factorial n : ℤ) + 1) (add_pos (LeanBridges.Counting.factorial_nat (n) (le_of_lt hH1)) (by norm_num)) s2)
  -- 4. def:prime, from 3
  have s4 : p > 1 := by exact (((Parley.Items.Stdlib.Divisibility.def_prime (p := p) s3a)).mp s3b).1
  -- 5. contradiction
  have s5 : p > n := by
    by_contra hS
    -- 5.1. inequalities, from S
    have s5_1 : p ≤ n := by linarith only [hS]
    -- 5.2. mun:factorial-divisible m := p, from 5.1
    have s5_2 : p ∣ (LeanBridges.Counting.factorial n : ℤ) := by exact (Parley.Items.Stdlib.Counting.mun_factorial_divisible (n := n) hH1 (m := p) s3a s5_1)
    -- 5.3. mun:divides-difference d := p, a := n! + 1, b := n!, from 3, 5.2
    have s5_3 : p ∣ (LeanBridges.Counting.factorial n : ℤ) + 1 - (LeanBridges.Counting.factorial n : ℤ) := by exact (Parley.Items.Stdlib.Divisibility.mun_divides_difference (d := p) (a := (LeanBridges.Counting.factorial n : ℤ) + 1) (b := (LeanBridges.Counting.factorial n : ℤ)) s3c s5_2)
    -- 5.4. substitute
    have s5_4 : p ∣ (1 : ℤ) := by
      have c1 : (LeanBridges.Counting.factorial n : ℤ) + 1 - (LeanBridges.Counting.factorial n : ℤ) = 1 := by parley_ring
      have row1 : p ∣ (1 : ℤ) := by (have h := Eq.subst (motive := (fun t : ℤ => p ∣ t)) c1 s5_3; push_cast at h ⊢; all_goals exact_mod_cast h)
      exact row1
    -- 5.5. mun:divides-one d := p, from 5.4
    have s5_5 : p = 1 := by exact (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := p) s3a s5_4)
    -- 5.6. inequalities
    have s5_6 : p ≠ 1 := ne_of_gt (by linarith only [s4])
    exact s5_6 s5_5
  -- 6. exhibit, from 3, 5
  exact ⟨p, s3a, ⟨s3b, s5⟩⟩

end Parley.Proofs.Wiedijk.InfinitelyManyPrimes.PrimeAbove
