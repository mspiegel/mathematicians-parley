module

public import AlgebraTactics
public import ArithTactics
public import PowerTactics
public import SubstTactics
public import Tactics
public import Parley.Items.Stdlib.Divisibility
public import Parley.Proofs.Hammack.Sqrt3Irrational.ThreePrime
public import Parley.Stdlib.Divisibility.CoprimeDivides

/-! Written from proofs/hammack/sqrt3-irrational.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.Sqrt3Irrational.ThreeDividesSquare

theorem three_divides_square (n : ℤ) (hH2 : (3 : ℤ) ∣ n ^ 2) :
    (3 : ℤ) ∣ n := by
  -- the theorem. contradiction
  have sThm : (3 : ℤ) ∣ n := by
    by_contra hc_hS
    have hS : ¬ (3 : ℤ) ∣ n := by parley_suppose hc_hS
    -- 1. thm:three-prime
    have s1 : Nat.Prime (3 : ℤ).toNat := by first | exact Parley.Proofs.Hammack.Sqrt3Irrational.ThreePrime.three_prime | exact (Parley.Proofs.Hammack.Sqrt3Irrational.ThreePrime.three_prime).symm | simpa using Parley.Proofs.Hammack.Sqrt3Irrational.ThreePrime.three_prime | exact_mod_cast Parley.Proofs.Hammack.Sqrt3Irrational.ThreePrime.three_prime | (have h := Parley.Proofs.Hammack.Sqrt3Irrational.ThreePrime.three_prime; parley_side)
    -- 2. calculation
    have s2 : (Int.gcd n (3 : ℤ) : ℤ) = 1 := by
      calc (Int.gcd n (3 : ℤ) : ℤ) = (Int.gcd (3 : ℤ) n : ℤ) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Divisibility.mun_gcd_commutes (a := n) (b := (3 : ℤ))) | (have h := (Parley.Items.Stdlib.Divisibility.mun_gcd_commutes (a := n) (b := (3 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_gcd_commutes (a := n) (b := (3 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_gcd_commutes (a := n) (b := (3 : ℤ))) | exact_mod_cast ((Parley.Items.Stdlib.Divisibility.mun_gcd_commutes (a := n) (b := (3 : ℤ)))).symm | (have h := (Parley.Items.Stdlib.Divisibility.mun_gcd_commutes (a := n) (b := (3 : ℤ))); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_gcd_commutes (a := n) (b := (3 : ℤ))); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_gcd_commutes (a := n) (b := (3 : ℤ))); parley_int_power h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_gcd_commutes (a := n) (b := (3 : ℤ))); parley_side)
        _ = 1 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Divisibility.mun_prime_coprime (p := 3) (by parley_side) (by parley_side) (a := n) (by parley_side)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_prime_coprime (p := 3) (by parley_side) (by parley_side) (a := n) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_prime_coprime (p := 3) (by parley_side) (by parley_side) (a := n) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_prime_coprime (p := 3) (by parley_side) (by parley_side) (a := n) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Divisibility.mun_prime_coprime (p := 3) (by parley_side) (by parley_side) (a := n) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Divisibility.mun_prime_coprime (p := 3) (by parley_side) (by parley_side) (a := n) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_prime_coprime (p := 3) (by parley_side) (by parley_side) (a := n) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_prime_coprime (p := 3) (by parley_side) (by parley_side) (a := n) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_prime_coprime (p := 3) (by parley_side) (by parley_side) (a := n) (by parley_side)); parley_side)
    -- 3. substitute
    have s3 : (3 : ℤ) ∣ n * n := by
      have c1 : n ^ 2 = n * n := by parley_ring
      have row1 : (3 : ℤ) ∣ n * n := by parley_subst_at c1 hH2
      exact row1
    -- 4. thm:coprime-divides x := n, c := n, n := 3, from 2, 3
    have s4 : (3 : ℤ) ∣ n := by first | exact (Parley.Stdlib.Divisibility.CoprimeDivides.coprime_divides (x := n) (c := n) (n := 3) (by parley_side) (by parley_side) (by parley_side)) | exact ((Parley.Stdlib.Divisibility.CoprimeDivides.coprime_divides (x := n) (c := n) (n := 3) (by parley_side) (by parley_side) (by parley_side))).symm | simpa using (Parley.Stdlib.Divisibility.CoprimeDivides.coprime_divides (x := n) (c := n) (n := 3) (by parley_side) (by parley_side) (by parley_side)) | exact_mod_cast (Parley.Stdlib.Divisibility.CoprimeDivides.coprime_divides (x := n) (c := n) (n := 3) (by parley_side) (by parley_side) (by parley_side)) | (have h := (Parley.Stdlib.Divisibility.CoprimeDivides.coprime_divides (x := n) (c := n) (n := 3) (by parley_side) (by parley_side) (by parley_side)); parley_side)
    all_goals parley_side
  all_goals parley_side

end Parley.Proofs.Hammack.Sqrt3Irrational.ThreeDividesSquare
