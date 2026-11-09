module

public import ArithTactics
public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Prime
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
  intro hS
  -- 4.1. def:prime p := 91, from S
  have s4_1 : ∀ d : ℤ, 0 < d → d ∣ (91 : ℤ) → d = 1 ∨ d = 91 := by exact (((Parley.Items.Stdlib.Divisibility.def_prime (p := (91 : ℤ)) (by parley_side))).mp hS).2
  -- 4.2. instantiate d := 7 in line 4.1
  have s4_2 : (7 : ℤ) ∣ (91 : ℤ) → (7 : ℤ) = 1 ∨ (7 : ℤ) = 91 := by exact (s4_1 (7 : ℤ) (by parley_side))
  -- 4.3. mun:modus-ponens, from 1, 4.2
  have s4_3 : (7 : ℤ) = 1 ∨ (7 : ℤ) = 91 := by exact (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := (7 : ℤ) ∣ (91 : ℤ)) (Q := (7 : ℤ) = 1 ∨ (7 : ℤ) = 91) s4_2 s1)
  -- 4.4. mun:disjunctive-syllogism, from 3, 4.3
  have s4_4 : (7 : ℤ) = 1 := by exact (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism (P := (7 : ℤ) = 1) (Q := (7 : ℤ) = 91) s4_3 s3)
  exact s2 s4_4

end Parley.Tests.Notations.Primes.NinetyOneIsNotPrime
