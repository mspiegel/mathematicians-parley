module

public import AlgebraTactics
public import ArithTactics
public import NormTactics
public import PowerTactics
public import SubstTactics
public import Tactics
public import Batteries.Tactic.Init
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Parley.Items.Stdlib.Divisibility
public import Parley.Proofs.Hammack.Sqrt3Irrational.ThreePrime

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
        _ = 1 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Divisibility.mun_prime_coprime (p := (3 : ℤ)) (by parley_side) s1 (a := n) hS) | (have h := (Parley.Items.Stdlib.Divisibility.mun_prime_coprime (p := (3 : ℤ)) (by parley_side) s1 (a := n) hS); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_prime_coprime (p := (3 : ℤ)) (by parley_side) s1 (a := n) hS); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_prime_coprime (p := (3 : ℤ)) (by parley_side) s1 (a := n) hS) | exact_mod_cast ((Parley.Items.Stdlib.Divisibility.mun_prime_coprime (p := (3 : ℤ)) (by parley_side) s1 (a := n) hS)).symm | (have h := (Parley.Items.Stdlib.Divisibility.mun_prime_coprime (p := (3 : ℤ)) (by parley_side) s1 (a := n) hS); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_prime_coprime (p := (3 : ℤ)) (by parley_side) s1 (a := n) hS); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_prime_coprime (p := (3 : ℤ)) (by parley_side) s1 (a := n) hS); parley_int_power h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_prime_coprime (p := (3 : ℤ)) (by parley_side) s1 (a := n) hS); parley_side)
    -- 3. substitute
    have s3 : (3 : ℤ) ∣ n * n := by
      have c1 : n ^ 2 = n * n := by parley_ring
      have row1 : (3 : ℤ) ∣ n * n := by parley_subst_at c1 hH2
      exact row1
    -- 4. thm:coprime-divides x := n, c := n, n := 3, from 2, 3
    have s4 : (3 : ℤ) ∣ n := by first | exact (Parley.Items.Stdlib.Divisibility.thm_coprime_divides (x := n) (c := n) (n := (3 : ℤ)) (by parley_side) s3 s2) | exact ((Parley.Items.Stdlib.Divisibility.thm_coprime_divides (x := n) (c := n) (n := (3 : ℤ)) (by parley_side) s3 s2)).symm | simpa using (Parley.Items.Stdlib.Divisibility.thm_coprime_divides (x := n) (c := n) (n := (3 : ℤ)) (by parley_side) s3 s2) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.thm_coprime_divides (x := n) (c := n) (n := (3 : ℤ)) (by parley_side) s3 s2) | (have h := (Parley.Items.Stdlib.Divisibility.thm_coprime_divides (x := n) (c := n) (n := (3 : ℤ)) (by parley_side) s3 s2); parley_side)
    all_goals parley_side
  all_goals parley_side

end Parley.Proofs.Hammack.Sqrt3Irrational.ThreeDividesSquare
