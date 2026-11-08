module

public import OrderTactics
public import SubstTactics
public import Tactics
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Rat.Init
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/wiedijk/sqrt2-irrational.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.Sqrt2Irrational.LowestTerms

theorem lowest_terms (x : ℚ) :
    (∃ p : ℤ, ∃ q : ℤ, (q > 0 ∧ x = (p : ℚ) / (q : ℚ)) ∧ ¬ (∃ d : ℤ, (d > 1 ∧ d ∣ p) ∧ d ∣ q)) := by
  -- 1. obtain p, q: mun:rational-coprime
  obtain ⟨p, q, s1a, ⟨s1b, s1c⟩⟩ := (Parley.Items.Stdlib.Numbers.mun_rational_coprime (x := x))
  -- 2. contradiction
  have s2 : ¬ (∃ d : ℤ, (d > 1 ∧ d ∣ p) ∧ d ∣ q) := by
    intro (hS : ∃ d : ℤ, (d > 1 ∧ d ∣ p) ∧ d ∣ q)
    -- 2.1. obtain d from S
    obtain ⟨d, ⟨⟨s2_1a, s2_1b⟩, s2_1c⟩⟩ := hS
    -- 2.2. thm:divides-gcd a := p, b := q, from 2.1
    have s2_2 : d ∣ (Int.gcd p q : ℤ) := by exact (Parley.Items.Stdlib.Divisibility.thm_divides_gcd (d := d) (a := p) (b := q) s2_1b s2_1c)
    -- 2.3. substitute gcd(p, q) = 1 (line 1) into line 2.2
    have s2_3 : d ∣ (1 : ℤ) := by first | parley_subst_at s1c s2_2 | (have e_nat : Int.gcd p q = 1 := by exact_mod_cast s1c; parley_subst_at e_nat s2_2)
    -- 2.4. mun:divides-one, from 2.3
    have r83_1 : 0 < d := by parley_order
    have r83_2 : 0 < d := by exact (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := d) r83_1)
    have s2_4 : d = 1 := by exact (Parley.Items.Stdlib.Divisibility.mun_divides_one (d := d) (by parley_side) s2_3)
    -- 2.5. inequalities
    have s2_5 : d ≠ 1 := by parley_side
    exact s2_5 s2_4
  -- 3. exhibit, from 1, 2
  exact ⟨p, q, ⟨⟨s1a, s1b⟩, s2⟩⟩

end Parley.Proofs.Wiedijk.Sqrt2Irrational.LowestTerms
