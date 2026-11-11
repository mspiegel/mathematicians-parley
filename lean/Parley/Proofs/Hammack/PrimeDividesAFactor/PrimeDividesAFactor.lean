module

public import AlgebraTactics
public import Tactics
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

/-! Written from proofs/hammack/prime-divides-a-factor.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.PrimeDividesAFactor.PrimeDividesAFactor

theorem prime_divides_a_factor (a : ℤ) (b : ℤ) (p : ℤ) (hH4 : Nat.Prime p.toNat) (hH5 : p ∣ a * b) :
    (p ∣ a ∨ p ∣ b) := by
  -- 1. mun:prime-nat, from H4
  have s1 : 0 < p := by exact (Parley.Items.Stdlib.Divisibility.mun_prime_nat (p := p) hH4)
  -- 2. axi:excluded-middle P := p divides a
  have s2 : p ∣ a ∨ ¬ p ∣ a := by exact (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := p ∣ a))
  -- 3. cases, from 2
  rcases s2 with hC1 | hC2
  · skip
    -- 3.1. mun:or-left Q := p divides b, from C1
    exact (Parley.Items.Stdlib.Reasoning.mun_or_left (P := p ∣ a) (Q := p ∣ b) hC1)
  · skip
    -- 3.2. mun:prime-coprime, from C2, H4, 1
    have s3_2 : (Int.gcd p a : ℤ) = 1 := by exact (Parley.Items.Stdlib.Divisibility.mun_prime_coprime (p := p) (by parley_side) hH4 (a := a) hC2)
    -- 3.3. substitute
    have s3_3 : (Int.gcd a p : ℤ) = 1 := by
      have c1 : (Int.gcd p a : ℤ) = (Int.gcd a p : ℤ) := by exact (Parley.Items.Stdlib.Divisibility.mun_gcd_commutes (a := p) (b := a))
      have row1 : (Int.gcd a p : ℤ) = 1 := by (have h := Eq.subst (motive := (fun t : ℤ => t = 1)) c1 s3_2; push_cast at h ⊢; all_goals exact_mod_cast h)
      exact row1
    -- 3.4. substitute
    have s3_4 : p ∣ b * a := by
      have c1 : a * b = b * a := by parley_ring
      have row1 : p ∣ b * a := by (have h := Eq.subst (motive := (fun t : ℤ => p ∣ t)) c1 hH5; push_cast at h ⊢; all_goals exact_mod_cast h)
      exact row1
    -- 3.5. thm:coprime-divides x := b, c := a, n := p, from 1, 3.3, 3.4
    have s3_5 : p ∣ b := by exact (Parley.Items.Stdlib.Divisibility.thm_coprime_divides (x := b) (c := a) (n := p) (by parley_side) s3_4 s3_3)
    -- 3.6. mun:or-right P := p divides a, from 3.5
    exact (Parley.Items.Stdlib.Reasoning.mun_or_right (P := p ∣ a) (Q := p ∣ b) s3_5)

end Parley.Proofs.Hammack.PrimeDividesAFactor.PrimeDividesAFactor
