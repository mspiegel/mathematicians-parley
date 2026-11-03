module

public import Counting
public import Tactics
public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Reasoning
public import Parley.Items.Stdlib.Sums

/-! Written from proofs/hammack/factorial-plus-k-not-prime.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.FactorialPlusKNotPrime.FactorialPlusKNotPrime

theorem factorial_plus_k_not_prime (n : ℕ) (hH1 : 0 < n) (k : ℤ) (hH2 : k ∈ Finset.Icc (2 : ℤ) (n : ℤ)) :
    ¬ Nat.Prime ((LeanBridges.Counting.factorial (n : ℤ) : ℤ) + k).toNat := by
  -- 1. mun:range-bounds a := 2, b := n, from H2
  have s1a : 2 ≤ k := by first | linarith [(Parley.Items.Stdlib.Sums.mun_range_bounds_1 (a := (2 : ℤ)) (b := (n : ℤ)) (k := k) hH2)] | (have h := (Parley.Items.Stdlib.Sums.mun_range_bounds_1 (a := (2 : ℤ)) (b := (n : ℤ)) (k := k) hH2); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_range_bounds_1 (a := (2 : ℤ)) (b := (n : ℤ)) (k := k) hH2) | (have h := (Parley.Items.Stdlib.Sums.mun_range_bounds_1 (a := (2 : ℤ)) (b := (n : ℤ)) (k := k) hH2); parley_side)
  have s1b : k ≤ (n : ℤ) := by first | linarith [(Parley.Items.Stdlib.Sums.mun_range_bounds_2 (a := (2 : ℤ)) (b := (n : ℤ)) (k := k) hH2)] | (have h := (Parley.Items.Stdlib.Sums.mun_range_bounds_2 (a := (2 : ℤ)) (b := (n : ℤ)) (k := k) hH2); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_range_bounds_2 (a := (2 : ℤ)) (b := (n : ℤ)) (k := k) hH2) | (have h := (Parley.Items.Stdlib.Sums.mun_range_bounds_2 (a := (2 : ℤ)) (b := (n : ℤ)) (k := k) hH2); parley_side)
  -- 2. inequalities, from 1
  have s2 : 0 < k := by parley_order
  -- 3. mun:pos-int-nat m := k, from 2
  have s3 : 0 < k := by first | exact (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := k) s2) | exact ((Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := k) s2)).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := k) s2) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := k) s2) | (have h := (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := k) s2); parley_side)
  lift k to ℕ using s3.le
  -- 4. mun:factorial-nat
  have s4 : 0 < (LeanBridges.Counting.factorial (n : ℤ) : ℤ) := by first | exact (Parley.Items.Stdlib.Counting.mun_factorial_nat (n := n)) | exact ((Parley.Items.Stdlib.Counting.mun_factorial_nat (n := n))).symm | simpa using (Parley.Items.Stdlib.Counting.mun_factorial_nat (n := n)) | exact_mod_cast (Parley.Items.Stdlib.Counting.mun_factorial_nat (n := n)) | (have h := (Parley.Items.Stdlib.Counting.mun_factorial_nat (n := n)); parley_side)
  -- 5. mun:nat-closure a := n!, b := k, from 3
  have s5 : 0 < (LeanBridges.Counting.factorial (n : ℤ) : ℤ) + (k : ℤ) := by first | exact (Parley.Items.Stdlib.Numbers.mun_nat_closure_1 (a := LeanBridges.Counting.factorial (n : ℤ)) (by parley_side) (b := k) (by parley_side)) | exact ((Parley.Items.Stdlib.Numbers.mun_nat_closure_1 (a := LeanBridges.Counting.factorial (n : ℤ)) (by parley_side) (b := k) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_nat_closure_1 (a := LeanBridges.Counting.factorial (n : ℤ)) (by parley_side) (b := k) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_nat_closure_1 (a := LeanBridges.Counting.factorial (n : ℤ)) (by parley_side) (b := k) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_nat_closure_1 (a := LeanBridges.Counting.factorial (n : ℤ)) (by parley_side) (b := k) (by parley_side)); parley_side)
  -- 6. mun:factorial-divisible m := k, from 1, 3
  have s6 : (k : ℤ) ∣ (LeanBridges.Counting.factorial (n : ℤ) : ℤ) := by first | exact (Parley.Items.Stdlib.Counting.mun_factorial_divisible (n := n) (by parley_side) (m := k) (by parley_side) (by parley_side)) | exact ((Parley.Items.Stdlib.Counting.mun_factorial_divisible (n := n) (by parley_side) (m := k) (by parley_side) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Counting.mun_factorial_divisible (n := n) (by parley_side) (m := k) (by parley_side) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Counting.mun_factorial_divisible (n := n) (by parley_side) (m := k) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Counting.mun_factorial_divisible (n := n) (by parley_side) (m := k) (by parley_side) (by parley_side)); parley_side)
  -- 7. mun:divides-self n := k
  have s7 : (k : ℤ) ∣ (k : ℤ) := by first | exact (Parley.Items.Stdlib.Divisibility.mun_divides_self (n := (k : ℤ))) | exact ((Parley.Items.Stdlib.Divisibility.mun_divides_self (n := (k : ℤ)))).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_divides_self (n := (k : ℤ))) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_divides_self (n := (k : ℤ))) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_self (n := (k : ℤ))); parley_side)
  -- 8. mun:divides-sum d := k, a := n!, b := k, from 6, 7
  have s8 : (k : ℤ) ∣ (LeanBridges.Counting.factorial (n : ℤ) : ℤ) + (k : ℤ) := by first | exact (Parley.Items.Stdlib.Divisibility.mun_divides_sum (d := (k : ℤ)) (a := (LeanBridges.Counting.factorial (n : ℤ) : ℤ)) (b := (k : ℤ)) s6 s7) | exact ((Parley.Items.Stdlib.Divisibility.mun_divides_sum (d := (k : ℤ)) (a := (LeanBridges.Counting.factorial (n : ℤ) : ℤ)) (b := (k : ℤ)) s6 s7)).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_divides_sum (d := (k : ℤ)) (a := (LeanBridges.Counting.factorial (n : ℤ) : ℤ)) (b := (k : ℤ)) s6 s7) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_divides_sum (d := (k : ℤ)) (a := (LeanBridges.Counting.factorial (n : ℤ) : ℤ)) (b := (k : ℤ)) s6 s7) | (have h := (Parley.Items.Stdlib.Divisibility.mun_divides_sum (d := (k : ℤ)) (a := (LeanBridges.Counting.factorial (n : ℤ) : ℤ)) (b := (k : ℤ)) s6 s7); parley_side)
  -- 9. contradiction
  have s9 : ¬ Nat.Prime ((LeanBridges.Counting.factorial (n : ℤ) : ℤ) + (k : ℤ)).toNat := by
    by_contra hc_hS
    have hS : Nat.Prime ((LeanBridges.Counting.factorial (n : ℤ) : ℤ) + (k : ℤ)).toNat := by parley_suppose hc_hS
    -- 9.1. def:prime p := n! + k, from S
    have r47_1 : 0 < (LeanBridges.Counting.factorial (n : ℤ) : ℤ) + (k : ℤ) := by parley_side
    have s9_1a : (LeanBridges.Counting.factorial (n : ℤ) : ℤ) + (k : ℤ) > 1 := by first | linarith [(((Parley.Items.Stdlib.Divisibility.def_prime (p := LeanBridges.Counting.factorial (n : ℤ) + k) (by parley_side))).mp (by parley_side)).1] | (have h := (((Parley.Items.Stdlib.Divisibility.def_prime (p := LeanBridges.Counting.factorial (n : ℤ) + k) (by parley_side))).mp (by parley_side)).1; push_cast at h; linarith) | exact_mod_cast (((Parley.Items.Stdlib.Divisibility.def_prime (p := LeanBridges.Counting.factorial (n : ℤ) + k) (by parley_side))).mp (by parley_side)).1 | (have h := (((Parley.Items.Stdlib.Divisibility.def_prime (p := LeanBridges.Counting.factorial (n : ℤ) + k) (by parley_side))).mp (by parley_side)).1; parley_side)
    have s9_1b : ∀ d : ℕ, 0 < d → (d : ℤ) ∣ (LeanBridges.Counting.factorial (n : ℤ) : ℤ) + (k : ℤ) → (d : ℤ) = 1 ∨ (d : ℤ) = (LeanBridges.Counting.factorial (n : ℤ) : ℤ) + (k : ℤ) := by first | exact (((Parley.Items.Stdlib.Divisibility.def_prime (p := LeanBridges.Counting.factorial (n : ℤ) + k) (by parley_side))).mp (by parley_side)).2 | exact ((((Parley.Items.Stdlib.Divisibility.def_prime (p := LeanBridges.Counting.factorial (n : ℤ) + k) (by parley_side))).mp (by parley_side)).2).symm | simpa using (((Parley.Items.Stdlib.Divisibility.def_prime (p := LeanBridges.Counting.factorial (n : ℤ) + k) (by parley_side))).mp (by parley_side)).2 | exact_mod_cast (((Parley.Items.Stdlib.Divisibility.def_prime (p := LeanBridges.Counting.factorial (n : ℤ) + k) (by parley_side))).mp (by parley_side)).2 | (have h := (((Parley.Items.Stdlib.Divisibility.def_prime (p := LeanBridges.Counting.factorial (n : ℤ) + k) (by parley_side))).mp (by parley_side)).2; parley_side)
    -- 9.2. instantiate d := k in line 9.1, from 3
    have s9_2 : (k : ℤ) ∣ (LeanBridges.Counting.factorial (n : ℤ) : ℤ) + (k : ℤ) → (k : ℤ) = 1 ∨ (k : ℤ) = (LeanBridges.Counting.factorial (n : ℤ) : ℤ) + (k : ℤ) := by first | exact (s9_1b k (by parley_side)) | exact ((s9_1b k (by parley_side))).symm | simpa using (s9_1b k (by parley_side)) | exact_mod_cast (s9_1b k (by parley_side)) | (have h := (s9_1b k (by parley_side)); parley_side)
    -- 9.3. mun:modus-ponens P := k divides n! + k, from 8, 9.2
    have s9_3 : (k : ℤ) = 1 ∨ (k : ℤ) = (LeanBridges.Counting.factorial (n : ℤ) : ℤ) + (k : ℤ) := by first | exact (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := (k : ℤ) ∣ (LeanBridges.Counting.factorial (n : ℤ) : ℤ) + (k : ℤ)) (Q := (k : ℤ) = 1 ∨ (k : ℤ) = (LeanBridges.Counting.factorial (n : ℤ) : ℤ) + (k : ℤ)) s9_2 s8) | exact ((Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := (k : ℤ) ∣ (LeanBridges.Counting.factorial (n : ℤ) : ℤ) + (k : ℤ)) (Q := (k : ℤ) = 1 ∨ (k : ℤ) = (LeanBridges.Counting.factorial (n : ℤ) : ℤ) + (k : ℤ)) s9_2 s8)).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := (k : ℤ) ∣ (LeanBridges.Counting.factorial (n : ℤ) : ℤ) + (k : ℤ)) (Q := (k : ℤ) = 1 ∨ (k : ℤ) = (LeanBridges.Counting.factorial (n : ℤ) : ℤ) + (k : ℤ)) s9_2 s8) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := (k : ℤ) ∣ (LeanBridges.Counting.factorial (n : ℤ) : ℤ) + (k : ℤ)) (Q := (k : ℤ) = 1 ∨ (k : ℤ) = (LeanBridges.Counting.factorial (n : ℤ) : ℤ) + (k : ℤ)) s9_2 s8) | (have h := (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := (k : ℤ) ∣ (LeanBridges.Counting.factorial (n : ℤ) : ℤ) + (k : ℤ)) (Q := (k : ℤ) = 1 ∨ (k : ℤ) = (LeanBridges.Counting.factorial (n : ℤ) : ℤ) + (k : ℤ)) s9_2 s8); parley_side)
    -- 9.4. cases, from 9.3
    have s9_4 : (k : ℤ) = (LeanBridges.Counting.factorial (n : ℤ) : ℤ) + (k : ℤ) := by
      rcases s9_3 with hC1 | hC2
      · skip
        -- 9.4.1. inequalities, from 1
        have s9_4_1 : 1 < (k : ℤ) := by parley_order
        -- 9.4.2. inequalities
        have s9_4_2 : 1 ≠ (k : ℤ) := by parley_side
        all_goals parley_side
      · skip
        all_goals parley_side
    -- 9.5. algebra, from 9.4
    have s9_5 : (LeanBridges.Counting.factorial (n : ℤ) : ℤ) = 0 := by linear_combination (norm := parley_norm) (-1) * s9_4
    -- 9.6. inequalities, from 4
    have s9_6 : (LeanBridges.Counting.factorial (n : ℤ) : ℤ) ≠ 0 := by parley_side
    all_goals parley_side
  all_goals exact s9

end Parley.Proofs.Hammack.FactorialPlusKNotPrime.FactorialPlusKNotPrime
