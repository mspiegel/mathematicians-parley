module

public import AlgebraTactics
public import PowerTactics
public import SubstTactics
public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Reasoning

/-! Written from proofs/hammack/prime-divides-a-factor.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.PrimeDividesAFactor.PrimeDividesAFactor

theorem prime_divides_a_factor (a : ℤ) (b : ℤ) (p : ℤ) (hH4 : Nat.Prime p.toNat) (hH5 : p ∣ a * b) :
    (p ∣ a ∨ p ∣ b) := by
  -- 1. mun:prime-nat, from H4
  have s1 : 0 < p := by first | exact (Parley.Items.Stdlib.Divisibility.mun_prime_nat (p := p) hH4) | exact ((Parley.Items.Stdlib.Divisibility.mun_prime_nat (p := p) hH4)).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_prime_nat (p := p) hH4) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_prime_nat (p := p) hH4) | (have h := (Parley.Items.Stdlib.Divisibility.mun_prime_nat (p := p) hH4); parley_side)
  -- 2. axi:excluded-middle P := p divides a
  have s2 : p ∣ a ∨ ¬ p ∣ a := by first | exact (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := p ∣ a)) | exact ((Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := p ∣ a))).symm | simpa using (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := p ∣ a)) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := p ∣ a)) | (have h := (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := p ∣ a)); parley_side)
  -- 3. cases, from 2
  have s3 : p ∣ a ∨ p ∣ b := by
    rcases s2 with hC1 | hC2
    · skip
      -- 3.1. mun:or-left Q := p divides b, from C1
      have s3_1 : p ∣ a ∨ p ∣ b := by first | exact (Parley.Items.Stdlib.Reasoning.mun_or_left (P := p ∣ a) (Q := p ∣ b) hC1) | exact ((Parley.Items.Stdlib.Reasoning.mun_or_left (P := p ∣ a) (Q := p ∣ b) hC1)).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_or_left (P := p ∣ a) (Q := p ∣ b) hC1) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_or_left (P := p ∣ a) (Q := p ∣ b) hC1) | (have h := (Parley.Items.Stdlib.Reasoning.mun_or_left (P := p ∣ a) (Q := p ∣ b) hC1); parley_side)
      all_goals parley_side
    · skip
      -- 3.2. mun:prime-coprime, from C2, H4, 1
      have s3_2 : (Int.gcd p a : ℤ) = 1 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Divisibility.mun_prime_coprime (p := p) (by parley_side) hH4 (a := a) hC2) | (have h := (Parley.Items.Stdlib.Divisibility.mun_prime_coprime (p := p) (by parley_side) hH4 (a := a) hC2); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_prime_coprime (p := p) (by parley_side) hH4 (a := a) hC2); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_prime_coprime (p := p) (by parley_side) hH4 (a := a) hC2) | exact_mod_cast ((Parley.Items.Stdlib.Divisibility.mun_prime_coprime (p := p) (by parley_side) hH4 (a := a) hC2)).symm | (have h := (Parley.Items.Stdlib.Divisibility.mun_prime_coprime (p := p) (by parley_side) hH4 (a := a) hC2); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_prime_coprime (p := p) (by parley_side) hH4 (a := a) hC2); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_prime_coprime (p := p) (by parley_side) hH4 (a := a) hC2); parley_int_power h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_prime_coprime (p := p) (by parley_side) hH4 (a := a) hC2); parley_side)
      -- 3.3. substitute
      have s3_3 : (Int.gcd a p : ℤ) = 1 := by
        have c1 : (Int.gcd p a : ℤ) = (Int.gcd a p : ℤ) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Divisibility.mun_gcd_commutes (a := p) (b := a)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_gcd_commutes (a := p) (b := a)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_gcd_commutes (a := p) (b := a)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_gcd_commutes (a := p) (b := a)) | exact_mod_cast ((Parley.Items.Stdlib.Divisibility.mun_gcd_commutes (a := p) (b := a))).symm | (have h := (Parley.Items.Stdlib.Divisibility.mun_gcd_commutes (a := p) (b := a)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_gcd_commutes (a := p) (b := a)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_gcd_commutes (a := p) (b := a)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_gcd_commutes (a := p) (b := a)); parley_side)
        have row1 : (Int.gcd a p : ℤ) = 1 := by parley_subst_at c1 s3_2
        exact row1
      -- 3.4. substitute
      have s3_4 : p ∣ b * a := by
        have c1 : a * b = b * a := by parley_ring
        have row1 : p ∣ b * a := by parley_subst_at c1 hH5
        exact row1
      -- 3.5. thm:coprime-divides x := b, c := a, n := p, from 1, 3.3, 3.4
      have s3_5 : p ∣ b := by first | exact (Parley.Items.Stdlib.Divisibility.thm_coprime_divides (x := b) (c := a) (n := p) (by parley_side) s3_4 s3_3) | exact ((Parley.Items.Stdlib.Divisibility.thm_coprime_divides (x := b) (c := a) (n := p) (by parley_side) s3_4 s3_3)).symm | simpa using (Parley.Items.Stdlib.Divisibility.thm_coprime_divides (x := b) (c := a) (n := p) (by parley_side) s3_4 s3_3) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.thm_coprime_divides (x := b) (c := a) (n := p) (by parley_side) s3_4 s3_3) | (have h := (Parley.Items.Stdlib.Divisibility.thm_coprime_divides (x := b) (c := a) (n := p) (by parley_side) s3_4 s3_3); parley_side)
      -- 3.6. mun:or-right P := p divides a, from 3.5
      have s3_6 : p ∣ a ∨ p ∣ b := by first | exact (Parley.Items.Stdlib.Reasoning.mun_or_right (P := p ∣ a) (Q := p ∣ b) s3_5) | exact ((Parley.Items.Stdlib.Reasoning.mun_or_right (P := p ∣ a) (Q := p ∣ b) s3_5)).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_or_right (P := p ∣ a) (Q := p ∣ b) s3_5) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_or_right (P := p ∣ a) (Q := p ∣ b) s3_5) | (have h := (Parley.Items.Stdlib.Reasoning.mun_or_right (P := p ∣ a) (Q := p ∣ b) s3_5); parley_side)
      all_goals parley_side
  all_goals exact s3

end Parley.Proofs.Hammack.PrimeDividesAFactor.PrimeDividesAFactor
