module

public import PowerTactics
public import Tactics
public import Parley.Items.Stdlib.Divisibility

/-! Written from proofs/wiedijk/wilson.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.Wilson.CoprimeBelowPrime

theorem coprime_below_prime (p : ℕ) (hH1 : 0 < p) (hH2 : Nat.Prime p) (a : ℕ) (hH3 : 0 < a) (hH4 : (a : ℤ) < (p : ℤ)) :
    (Int.gcd (a : ℤ) (p : ℤ) : ℤ) = 1 := by
  -- 1. mun:below-not-divisible n := p, x := a, from H4
  have s1 : ¬ (p : ℤ) ∣ (a : ℤ) := by first | exact (Parley.Items.Stdlib.Divisibility.mun_below_not_divisible (n := p) (by parley_side) (x := a) (by parley_side) (by parley_side)) | exact ((Parley.Items.Stdlib.Divisibility.mun_below_not_divisible (n := p) (by parley_side) (x := a) (by parley_side) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_below_not_divisible (n := p) (by parley_side) (x := a) (by parley_side) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_below_not_divisible (n := p) (by parley_side) (x := a) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_below_not_divisible (n := p) (by parley_side) (x := a) (by parley_side) (by parley_side)); parley_side)
  -- 2. calculation
  have s2 : (Int.gcd (a : ℤ) (p : ℤ) : ℤ) = 1 := by
    calc (Int.gcd (a : ℤ) (p : ℤ) : ℤ) = (Int.gcd (p : ℤ) (a : ℤ) : ℤ) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Divisibility.mun_gcd_commutes (a := (a : ℤ)) (b := (p : ℤ))) | (have h := (Parley.Items.Stdlib.Divisibility.mun_gcd_commutes (a := (a : ℤ)) (b := (p : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_gcd_commutes (a := (a : ℤ)) (b := (p : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_gcd_commutes (a := (a : ℤ)) (b := (p : ℤ))) | exact_mod_cast ((Parley.Items.Stdlib.Divisibility.mun_gcd_commutes (a := (a : ℤ)) (b := (p : ℤ)))).symm | (have h := (Parley.Items.Stdlib.Divisibility.mun_gcd_commutes (a := (a : ℤ)) (b := (p : ℤ))); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_gcd_commutes (a := (a : ℤ)) (b := (p : ℤ))); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_gcd_commutes (a := (a : ℤ)) (b := (p : ℤ))); parley_int_power h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_gcd_commutes (a := (a : ℤ)) (b := (p : ℤ))); parley_side)
      _ = 1 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Divisibility.mun_prime_coprime (p := p) (by parley_side) (by parley_side) (a := (a : ℤ)) (by parley_side)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_prime_coprime (p := p) (by parley_side) (by parley_side) (a := (a : ℤ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_prime_coprime (p := p) (by parley_side) (by parley_side) (a := (a : ℤ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_prime_coprime (p := p) (by parley_side) (by parley_side) (a := (a : ℤ)) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Divisibility.mun_prime_coprime (p := p) (by parley_side) (by parley_side) (a := (a : ℤ)) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Divisibility.mun_prime_coprime (p := p) (by parley_side) (by parley_side) (a := (a : ℤ)) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_prime_coprime (p := p) (by parley_side) (by parley_side) (a := (a : ℤ)) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_prime_coprime (p := p) (by parley_side) (by parley_side) (a := (a : ℤ)) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_prime_coprime (p := p) (by parley_side) (by parley_side) (a := (a : ℤ)) (by parley_side)); parley_side)
  all_goals exact s2

end Parley.Proofs.Wiedijk.Wilson.CoprimeBelowPrime
