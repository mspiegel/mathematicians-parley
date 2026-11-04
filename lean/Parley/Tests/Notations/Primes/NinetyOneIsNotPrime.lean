module

public import ArithTactics
public import PowerTactics
public import Tactics
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Reasoning

/-! Written from tests/notations/primes.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Primes.NinetyOneIsNotPrime

theorem ninety_one_is_not_prime :
    ¬ Nat.Prime (91 : ℤ).toNat := by
  -- 1. arithmetic
  have s1 : (7 : ℤ) ∣ (91 : ℤ) := by parley_arith
  -- 2. arithmetic
  have s2 : (7 : ℤ) ≠ 1 := by parley_arith
  -- 3. arithmetic
  have s3 : (7 : ℤ) ≠ 91 := by parley_arith
  -- 4. contradiction
  have s4 : ¬ Nat.Prime (91 : ℤ).toNat := by
    by_contra hc_hS
    have hS : Nat.Prime (91 : ℤ).toNat := by parley_suppose hc_hS
    -- 4.1. def:prime p := 91, from S
    have s4_1 : ∀ d : ℕ, 0 < d → (d : ℤ) ∣ (91 : ℤ) → (d : ℤ) = 1 ∨ (d : ℤ) = 91 := by first | exact (((Parley.Items.Stdlib.Divisibility.def_prime (p := 91) (by parley_side))).mp (by parley_side)).2 | exact ((((Parley.Items.Stdlib.Divisibility.def_prime (p := 91) (by parley_side))).mp (by parley_side)).2).symm | simpa using (((Parley.Items.Stdlib.Divisibility.def_prime (p := 91) (by parley_side))).mp (by parley_side)).2 | exact_mod_cast (((Parley.Items.Stdlib.Divisibility.def_prime (p := 91) (by parley_side))).mp (by parley_side)).2 | (have h := (((Parley.Items.Stdlib.Divisibility.def_prime (p := 91) (by parley_side))).mp (by parley_side)).2; parley_side)
    -- 4.2. instantiate d := 7 in line 4.1
    have s4_2 : (7 : ℤ) ∣ (91 : ℤ) → (7 : ℤ) = 1 ∨ (7 : ℤ) = 91 := by first | exact (s4_1 7 (by parley_side)) | exact ((s4_1 7 (by parley_side))).symm | simpa using (s4_1 7 (by parley_side)) | exact_mod_cast (s4_1 7 (by parley_side)) | (have h := (s4_1 7 (by parley_side)); parley_side)
    -- 4.3. mun:modus-ponens, from 1, 4.2
    have s4_3 : (7 : ℤ) = 1 ∨ (7 : ℤ) = 91 := by first | exact (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := (7 : ℤ) ∣ (91 : ℤ)) (Q := (7 : ℤ) = 1 ∨ (7 : ℤ) = 91) s4_2 s1) | exact ((Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := (7 : ℤ) ∣ (91 : ℤ)) (Q := (7 : ℤ) = 1 ∨ (7 : ℤ) = 91) s4_2 s1)).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := (7 : ℤ) ∣ (91 : ℤ)) (Q := (7 : ℤ) = 1 ∨ (7 : ℤ) = 91) s4_2 s1) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := (7 : ℤ) ∣ (91 : ℤ)) (Q := (7 : ℤ) = 1 ∨ (7 : ℤ) = 91) s4_2 s1) | (have h := (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := (7 : ℤ) ∣ (91 : ℤ)) (Q := (7 : ℤ) = 1 ∨ (7 : ℤ) = 91) s4_2 s1); parley_side)
    -- 4.4. mun:disjunctive-syllogism, from 3, 4.3
    have s4_4 : (7 : ℤ) = 1 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism (P := (7 : ℤ) = 1) (Q := (7 : ℤ) = 91) s4_3 s3) | (have h := (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism (P := (7 : ℤ) = 1) (Q := (7 : ℤ) = 91) s4_3 s3); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism (P := (7 : ℤ) = 1) (Q := (7 : ℤ) = 91) s4_3 s3); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism (P := (7 : ℤ) = 1) (Q := (7 : ℤ) = 91) s4_3 s3) | exact_mod_cast ((Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism (P := (7 : ℤ) = 1) (Q := (7 : ℤ) = 91) s4_3 s3)).symm | (have h := (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism (P := (7 : ℤ) = 1) (Q := (7 : ℤ) = 91) s4_3 s3); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism (P := (7 : ℤ) = 1) (Q := (7 : ℤ) = 91) s4_3 s3); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism (P := (7 : ℤ) = 1) (Q := (7 : ℤ) = 91) s4_3 s3); parley_int_power h) | (have h := (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism (P := (7 : ℤ) = 1) (Q := (7 : ℤ) = 91) s4_3 s3); parley_side)
    all_goals parley_side
  all_goals exact s4

end Parley.Tests.Notations.Primes.NinetyOneIsNotPrime
