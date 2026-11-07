module

public import AlgebraTactics
public import ArithTactics
public import Counting
public import FactorialTactics
public import NormTactics
public import OrderTactics
public import PowerTactics
public import SubstTactics
public import Tactics
public import Batteries.Tactic.Init
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Divisibility

/-! Written from proofs/wiedijk/infinitely-many-primes.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.InfinitelyManyPrimes.PrimeAbove

set_option maxHeartbeats 400000 in
theorem prime_above (n : ℤ) (hH1 : 0 < n) :
    (∃ p : ℤ, 0 < p ∧ (Nat.Prime p.toNat ∧ p > n)) := by
  -- 1. mun:factorial-nat
  have s1 : 0 < (LeanBridges.Counting.factorial n : ℤ) := by first | exact (Parley.Items.Stdlib.Counting.mun_factorial_nat (n := n) (by parley_side)) | exact ((Parley.Items.Stdlib.Counting.mun_factorial_nat (n := n) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Counting.mun_factorial_nat (n := n) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Counting.mun_factorial_nat (n := n) (by parley_side)) | (have h := (Parley.Items.Stdlib.Counting.mun_factorial_nat (n := n) (by parley_side)); parley_side)
  -- 2. inequalities, from 1
  have s2 : (LeanBridges.Counting.factorial n : ℤ) + 1 > 1 := by parley_order
  -- 3. obtain p: thm:prime-factor m := n! + 1, from 2
  obtain ⟨p, s3a, ⟨s3b, s3c⟩⟩ := (Parley.Items.Stdlib.Divisibility.thm_prime_factor (m := (LeanBridges.Counting.factorial n : ℤ) + 1) (by parley_side) (by parley_side))
  -- 4. def:prime, from 3
  have s4 : p > 1 := by first | linarith [((Parley.Items.Stdlib.Divisibility.def_prime (p := p) (by parley_side))).mp (by parley_side)] | (have h := ((Parley.Items.Stdlib.Divisibility.def_prime (p := p) (by parley_side))).mp (by parley_side); push_cast at h; linarith) | exact_mod_cast ((Parley.Items.Stdlib.Divisibility.def_prime (p := p) (by parley_side))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Divisibility.def_prime (p := p) (by parley_side))).mp (by parley_side); parley_side)
  -- 5. contradiction
  have s5 : p > n := by
    by_contra hc_hS
    have hS : ¬ p > n := by parley_suppose hc_hS
    -- 5.1. inequalities, from S
    have s5_1 : p ≤ n := by parley_order
    -- 5.2. mun:factorial-divisible m := p, from 5.1
    have s5_2 : p ∣ (LeanBridges.Counting.factorial n : ℤ) := by first | exact (Parley.Items.Stdlib.Counting.mun_factorial_divisible (n := n) (by parley_side) (m := p) (by parley_side) s5_1) | exact ((Parley.Items.Stdlib.Counting.mun_factorial_divisible (n := n) (by parley_side) (m := p) (by parley_side) s5_1)).symm | simpa using (Parley.Items.Stdlib.Counting.mun_factorial_divisible (n := n) (by parley_side) (m := p) (by parley_side) s5_1) | exact_mod_cast (Parley.Items.Stdlib.Counting.mun_factorial_divisible (n := n) (by parley_side) (m := p) (by parley_side) s5_1) | (have h := (Parley.Items.Stdlib.Counting.mun_factorial_divisible (n := n) (by parley_side) (m := p) (by parley_side) s5_1); parley_side)
    -- 5.3. mun:divides-difference d := p, a := n! + 1, b := n!, from 3, 5.2
    have s5_3 : p ∣ (LeanBridges.Counting.factorial n : ℤ) + 1 - (LeanBridges.Counting.factorial n : ℤ) := by first | exact (Parley.Items.Stdlib.Divisibility.mun_divides_difference (d := p) (a := (LeanBridges.Counting.factorial n : ℤ) + 1) (b := (LeanBridges.Counting.factorial n : ℤ)) s3c s5_2) | exact ((Parley.Items.Stdlib.Divisibility.mun_divides_difference (d := p) (a := (LeanBridges.Counting.factorial n : ℤ) + 1) (b := (LeanBridges.Counting.factorial n : ℤ)) s3c s5_2)).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_divides_difference (d := p) (a := (LeanBridges.Counting.factorial n : ℤ) + 1) (b := (LeanBridges.Counting.factorial n : ℤ)) s3c s5_2) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_divides_difference (d := p) (a := (LeanBridges.Counting.factorial n : ℤ) + 1) (b := (LeanBridges.Counting.factorial n : ℤ)) s3c s5_2) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_difference (d := p) (a := (LeanBridges.Counting.factorial n : ℤ) + 1) (b := (LeanBridges.Counting.factorial n : ℤ)) s3c s5_2); parley_side)
    -- 5.4. substitute
    have s5_4 : p ∣ (1 : ℤ) := by
      have c1 : (LeanBridges.Counting.factorial n : ℤ) + 1 - (LeanBridges.Counting.factorial n : ℤ) = 1 := by parley_ring
      have row1 : p ∣ (1 : ℤ) := by parley_subst_at c1 s5_3
      exact row1
    -- 5.5. mun:divides-one d := p, from 5.4
    have s5_5 : p = 1 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := p) (by parley_side) s5_4) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := p) (by parley_side) s5_4); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := p) (by parley_side) s5_4); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := p) (by parley_side) s5_4) | exact_mod_cast ((Parley.Items.Stdlib.Divisibility.mun_divides_one (d := p) (by parley_side) s5_4)).symm | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := p) (by parley_side) s5_4); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := p) (by parley_side) s5_4); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := p) (by parley_side) s5_4); parley_int_power h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := p) (by parley_side) s5_4); parley_side)
    -- 5.6. inequalities
    have s5_6 : p ≠ 1 := by parley_side
    all_goals parley_side
  -- 6. exhibit, from 3, 5
  have s6 : ∃ p : ℤ, 0 < p ∧ (Nat.Prime p.toNat ∧ p > n) := ⟨p, by parley_side, ⟨by parley_side, by parley_side⟩⟩
  all_goals exact s6

end Parley.Proofs.Wiedijk.InfinitelyManyPrimes.PrimeAbove
