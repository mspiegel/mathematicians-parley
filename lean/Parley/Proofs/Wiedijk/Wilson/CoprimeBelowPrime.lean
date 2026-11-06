module

public import PowerTactics
public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Parley.Items.Stdlib.Divisibility

/-! Written from proofs/wiedijk/wilson.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.Wilson.CoprimeBelowPrime

theorem coprime_below_prime (p : ℤ) (hH1 : 0 < p) (hH2 : Nat.Prime p.toNat) (a : ℤ) (hH3 : 0 < a) (hH4 : a < p) :
    (Int.gcd a p : ℤ) = 1 := by
  -- 1. mun:below-not-divisible n := p, x := a, from H4
  have s1 : ¬ p ∣ a := by first | exact (Parley.Items.Stdlib.Divisibility.mun_below_not_divisible (n := p) (by parley_side) (x := a) (by parley_side) hH4) | exact ((Parley.Items.Stdlib.Divisibility.mun_below_not_divisible (n := p) (by parley_side) (x := a) (by parley_side) hH4)).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_below_not_divisible (n := p) (by parley_side) (x := a) (by parley_side) hH4) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_below_not_divisible (n := p) (by parley_side) (x := a) (by parley_side) hH4) | (have h := (Parley.Items.Stdlib.Divisibility.mun_below_not_divisible (n := p) (by parley_side) (x := a) (by parley_side) hH4); parley_side)
  -- 2. calculation
  have s2 : (Int.gcd a p : ℤ) = 1 := by
    calc (Int.gcd a p : ℤ) = (Int.gcd p a : ℤ) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Divisibility.mun_gcd_commutes (a := a) (b := p)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_gcd_commutes (a := a) (b := p)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_gcd_commutes (a := a) (b := p)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_gcd_commutes (a := a) (b := p)) | exact_mod_cast ((Parley.Items.Stdlib.Divisibility.mun_gcd_commutes (a := a) (b := p))).symm | (have h := (Parley.Items.Stdlib.Divisibility.mun_gcd_commutes (a := a) (b := p)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_gcd_commutes (a := a) (b := p)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_gcd_commutes (a := a) (b := p)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_gcd_commutes (a := a) (b := p)); parley_side)
      _ = 1 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Divisibility.mun_prime_coprime (p := p) (by parley_side) hH2 (a := a) s1) | (have h := (Parley.Items.Stdlib.Divisibility.mun_prime_coprime (p := p) (by parley_side) hH2 (a := a) s1); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_prime_coprime (p := p) (by parley_side) hH2 (a := a) s1); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_prime_coprime (p := p) (by parley_side) hH2 (a := a) s1) | exact_mod_cast ((Parley.Items.Stdlib.Divisibility.mun_prime_coprime (p := p) (by parley_side) hH2 (a := a) s1)).symm | (have h := (Parley.Items.Stdlib.Divisibility.mun_prime_coprime (p := p) (by parley_side) hH2 (a := a) s1); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_prime_coprime (p := p) (by parley_side) hH2 (a := a) s1); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_prime_coprime (p := p) (by parley_side) hH2 (a := a) s1); parley_int_power h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_prime_coprime (p := p) (by parley_side) hH2 (a := a) s1); parley_side)
  all_goals exact s2

end Parley.Proofs.Wiedijk.Wilson.CoprimeBelowPrime
