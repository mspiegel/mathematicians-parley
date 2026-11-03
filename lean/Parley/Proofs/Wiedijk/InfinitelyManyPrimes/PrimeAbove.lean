module

public import Counting
public import Tactics
public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Divisibility

/-! Written from proofs/wiedijk/infinitely-many-primes.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.InfinitelyManyPrimes.PrimeAbove

theorem prime_above (n : ℕ) (hH1 : 0 < n) :
    (∃ p : ℕ, 0 < p ∧ (Nat.Prime p ∧ (p : ℤ) > (n : ℤ))) := by
  -- 1. mun:factorial-nat
  have s1 : 0 < (LeanBridges.Counting.factorial (n : ℤ) : ℤ) := by first | exact (Parley.Items.Stdlib.Counting.mun_factorial_nat (n := n)) | exact ((Parley.Items.Stdlib.Counting.mun_factorial_nat (n := n))).symm | simpa using (Parley.Items.Stdlib.Counting.mun_factorial_nat (n := n)) | exact_mod_cast (Parley.Items.Stdlib.Counting.mun_factorial_nat (n := n)) | (have h := (Parley.Items.Stdlib.Counting.mun_factorial_nat (n := n)); parley_side)
  -- 2. inequalities, from 1
  have s2 : (LeanBridges.Counting.factorial (n : ℤ) : ℤ) + 1 > 1 := by parley_order
  -- 3. obtain p: thm:prime-factor m := n! + 1, from 2
  obtain ⟨p, s3a, ⟨s3b, s3c⟩⟩ := (Parley.Items.Stdlib.Divisibility.thm_prime_factor (m := LeanBridges.Counting.factorial (n : ℤ) + 1) (by parley_side) (by parley_side))
  -- 4. def:prime, from 3
  have s4 : (p : ℤ) > 1 := by first | linarith [((Parley.Items.Stdlib.Divisibility.def_prime (p := p) (by parley_side))).mp (by parley_side)] | (have h := ((Parley.Items.Stdlib.Divisibility.def_prime (p := p) (by parley_side))).mp (by parley_side); push_cast at h; linarith) | exact_mod_cast ((Parley.Items.Stdlib.Divisibility.def_prime (p := p) (by parley_side))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Divisibility.def_prime (p := p) (by parley_side))).mp (by parley_side); parley_side)
  -- 5. contradiction
  have s5 : (p : ℤ) > (n : ℤ) := by
    by_contra hc_hS
    have hS : ¬ (p : ℤ) > (n : ℤ) := by parley_suppose hc_hS
    -- 5.1. inequalities, from S
    have s5_1 : (p : ℤ) ≤ (n : ℤ) := by parley_order
    -- 5.2. mun:factorial-divisible m := p, from 5.1
    have s5_2 : (p : ℤ) ∣ (LeanBridges.Counting.factorial (n : ℤ) : ℤ) := by first | exact (Parley.Items.Stdlib.Counting.mun_factorial_divisible (n := n) (by parley_side) (m := p) (by parley_side) (by parley_side)) | exact ((Parley.Items.Stdlib.Counting.mun_factorial_divisible (n := n) (by parley_side) (m := p) (by parley_side) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Counting.mun_factorial_divisible (n := n) (by parley_side) (m := p) (by parley_side) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Counting.mun_factorial_divisible (n := n) (by parley_side) (m := p) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Counting.mun_factorial_divisible (n := n) (by parley_side) (m := p) (by parley_side) (by parley_side)); parley_side)
    -- 5.3. mun:divides-difference d := p, a := n! + 1, b := n!, from 3, 5.2
    have s5_3 : (p : ℤ) ∣ (LeanBridges.Counting.factorial (n : ℤ) : ℤ) + 1 - (LeanBridges.Counting.factorial (n : ℤ) : ℤ) := by first | exact (Parley.Items.Stdlib.Divisibility.mun_divides_difference (d := (p : ℤ)) (a := (LeanBridges.Counting.factorial (n : ℤ) : ℤ) + 1) (b := (LeanBridges.Counting.factorial (n : ℤ) : ℤ)) s3c s5_2) | exact ((Parley.Items.Stdlib.Divisibility.mun_divides_difference (d := (p : ℤ)) (a := (LeanBridges.Counting.factorial (n : ℤ) : ℤ) + 1) (b := (LeanBridges.Counting.factorial (n : ℤ) : ℤ)) s3c s5_2)).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_divides_difference (d := (p : ℤ)) (a := (LeanBridges.Counting.factorial (n : ℤ) : ℤ) + 1) (b := (LeanBridges.Counting.factorial (n : ℤ) : ℤ)) s3c s5_2) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_divides_difference (d := (p : ℤ)) (a := (LeanBridges.Counting.factorial (n : ℤ) : ℤ) + 1) (b := (LeanBridges.Counting.factorial (n : ℤ) : ℤ)) s3c s5_2) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_difference (d := (p : ℤ)) (a := (LeanBridges.Counting.factorial (n : ℤ) : ℤ) + 1) (b := (LeanBridges.Counting.factorial (n : ℤ) : ℤ)) s3c s5_2); parley_side)
    -- 5.4. substitute
    have s5_4 : (p : ℤ) ∣ (1 : ℤ) := by
      have c1 : (LeanBridges.Counting.factorial (n : ℤ) : ℤ) + 1 - (LeanBridges.Counting.factorial (n : ℤ) : ℤ) = 1 := by parley_ring
      have row1 : (p : ℤ) ∣ (1 : ℤ) := by parley_subst_at c1 s5_3
      exact row1
    -- 5.5. mun:divides-one d := p, from 5.4
    have s5_5 : (p : ℤ) = 1 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := p) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := p) (by parley_side) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := p) (by parley_side) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := p) (by parley_side) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Divisibility.mun_divides_one (d := p) (by parley_side) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := p) (by parley_side) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := p) (by parley_side) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := p) (by parley_side) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := p) (by parley_side) (by parley_side)); parley_side)
    -- 5.6. inequalities
    have s5_6 : (p : ℤ) ≠ 1 := by parley_side
    all_goals parley_side
  -- 6. exhibit, from 3, 5
  have s6 : ∃ p : ℕ, 0 < p ∧ (Nat.Prime p ∧ (p : ℤ) > (n : ℤ)) := ⟨p, by parley_side, ⟨by parley_side, by parley_side⟩⟩
  all_goals exact s6

end Parley.Proofs.Wiedijk.InfinitelyManyPrimes.PrimeAbove
