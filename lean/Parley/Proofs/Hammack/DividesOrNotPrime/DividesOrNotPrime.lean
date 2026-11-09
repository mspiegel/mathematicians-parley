module

public import SubstTactics
public import Tactics
public import Batteries.Tactic.Init
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Reasoning

/-! Written from proofs/hammack/divides-or-not-prime.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.DividesOrNotPrime.DividesOrNotPrime

set_option maxHeartbeats 400000 in
theorem divides_or_not_prime (a : ℤ) (hH1 : 0 < a) (b : ℤ) (hH2 : 0 < b) (hH3 : (Int.gcd a b : ℤ) > 1) :
    (b ∣ a ∨ ¬ Nat.Prime b.toNat) := by
  -- the theorem. contradiction
  by_contra hS
  -- 1. mun:not-either, from S
  have s1a : ¬ b ∣ a := by exact (((Parley.Items.Stdlib.Reasoning.mun_not_either (P := b ∣ a) (Q := ¬ Nat.Prime b.toNat))).mp hS).1
  have s1b : ¬ ¬ Nat.Prime b.toNat := by exact (((Parley.Items.Stdlib.Reasoning.mun_not_either (P := b ∣ a) (Q := ¬ Nat.Prime b.toNat))).mp hS).2
  -- 2. mun:double-negation, from 1
  have s2 : Nat.Prime b.toNat := by exact (Parley.Items.Stdlib.Reasoning.mun_double_negation (P := Nat.Prime b.toNat) s1b)
  -- 3. def:prime p := b, from 2
  have s3a : b > 1 := by exact (((Parley.Items.Stdlib.Divisibility.def_prime (p := b) (by parley_side))).mp s2).1
  have s3b : ∀ d : ℤ, 0 < d → d ∣ b → d = 1 ∨ d = b := by exact (((Parley.Items.Stdlib.Divisibility.def_prime (p := b) (by parley_side))).mp s2).2
  -- 4. def:gcd
  have s4a : 0 < (Int.gcd a b : ℤ) := by exact (Parley.Items.Stdlib.Divisibility.def_gcd_1 (a := a) (by parley_side) (b := b) (by parley_side))
  have s4b : (Int.gcd a b : ℤ) ∣ b := by exact (Parley.Items.Stdlib.Divisibility.def_gcd_3 (a := a) (by parley_side) (b := b) (by parley_side))
  -- 5. instantiate d := gcd(a, b) in line 3, from 4
  have s5 : (Int.gcd a b : ℤ) ∣ b → (Int.gcd a b : ℤ) = 1 ∨ (Int.gcd a b : ℤ) = b := by exact (s3b (Int.gcd a b : ℤ) (by parley_side))
  -- 6. mun:modus-ponens P := gcd(a, b) divides b, from 4, 5
  have s6 : (Int.gcd a b : ℤ) = 1 ∨ (Int.gcd a b : ℤ) = b := by exact (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := (Int.gcd a b : ℤ) ∣ b) (Q := (Int.gcd a b : ℤ) = 1 ∨ (Int.gcd a b : ℤ) = b) s5 s4b)
  -- 7. def:gcd
  have s7 : (Int.gcd a b : ℤ) ∣ a := by exact (Parley.Items.Stdlib.Divisibility.def_gcd_2 (a := a) (by parley_side) (b := b) (by parley_side))
  -- 8. cases, from 6
  have s8 : b ∣ a := by
    rcases s6 with hC1 | hC2
    · skip
      -- 8.1. inequalities
      have s8_1 : (Int.gcd a b : ℤ) ≠ 1 := by parley_side
      exact absurd hC1 s8_1
    · skip
      -- 8.2. substitute gcd(a, b) = b (C2) into line 7
      parley_subst_at hC2 s7
  exact s1a s8

end Parley.Proofs.Hammack.DividesOrNotPrime.DividesOrNotPrime
