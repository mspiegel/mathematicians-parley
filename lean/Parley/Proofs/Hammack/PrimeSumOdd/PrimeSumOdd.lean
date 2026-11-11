module

public import ArithTactics
public import NormTactics
public import OrderTactics
public import Tactics
public import Mathlib.Algebra.Group.Even
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Reasoning

/-! Written from proofs/hammack/prime-sum-odd.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.PrimeSumOdd.PrimeSumOdd

theorem prime_sum_odd (p : ℤ) (hH1 : 0 < p) (q : ℤ) (hH2 : 0 < q) (hH3 : Nat.Prime p.toNat) (hH4 : Nat.Prime q.toNat) (hH5 : p < q) :
    Odd (2 * p + q ^ 2) := by
  -- 1. def:prime, from H3
  have s1 : p > 1 := by exact (((Parley.Items.Stdlib.Divisibility.def_prime (p := p) hH1)).mp hH3).1
  -- 2. mun:integer-step m := 1, n := p, from 1
  have s2 : 1 + 1 ≤ p := by exact (Parley.Items.Stdlib.Numbers.mun_integer_step (m := (1 : ℤ)) (n := p) s1)
  -- 3. transitivity, from 2, H5
  have s3 : 1 + 1 < q := by parley_order
  -- 4. def:prime p := q, from H4
  have s4 : ∀ d : ℤ, 0 < d → d ∣ q → d = 1 ∨ d = q := by exact (((Parley.Items.Stdlib.Divisibility.def_prime (p := q) hH2)).mp hH4).2
  -- 5. mun:even-or-odd n := q
  have s5 : Even q ∨ Odd q := by exact (Parley.Items.Stdlib.Divisibility.mun_even_or_odd (n := q))
  -- 6. cases, from 5
  have s6 : Odd q := by
    rcases s5 with hC1 | hC4
    · skip
      -- 6.1. obtain k: def:even n := q, from C1
      obtain ⟨k, s6_1⟩ := ((Parley.Items.Stdlib.Divisibility.def_even (n := q))).mp hC1
      -- 6.2. def:divides d := 2, n := q, from 6.1
      have s6_2 : (2 : ℤ) ∣ q := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (2 : ℤ)) (n := q))).mpr ⟨k, s6_1⟩
      -- 6.3. instantiate d := 2 in line 4
      have s6_3 : (2 : ℤ) ∣ q → (2 : ℤ) = 1 ∨ 2 = q := by exact (s4 (2 : ℤ) (by parley_side))
      -- 6.4. mun:modus-ponens P := 2 divides q, from 6.2, 6.3
      have s6_4 : (2 : ℤ) = 1 ∨ 2 = q := by exact (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := (2 : ℤ) ∣ q) (Q := (2 : ℤ) = 1 ∨ 2 = q) s6_3 s6_2)
      -- 6.5. cases, from 6.4
      have s6_5 : 2 = q := by
        rcases s6_4 with hC2 | hC3
        · skip
          -- 6.5.1. arithmetic
          have s6_5_1 : (2 : ℤ) ≠ 1 := by parley_arith
          exact absurd hC2 s6_5_1
        · skip
          exact hC3
      -- 6.6. inequalities
      have s6_6 : 2 ≠ q := by parley_side
      exact absurd s6_5 s6_6
    · skip
      exact hC4
  -- 7. obtain k: def:odd n := q, from 6
  obtain ⟨k, s7⟩ := ((Parley.Items.Stdlib.Divisibility.def_odd (n := q))).mp s6
  -- 8. algebra, from 7
  have s8 : 2 * p + q ^ 2 = 2 * (p + 2 * k ^ 2 + 2 * k) + 1 := by linear_combination (norm := parley_norm) (2 * k + q + 1) * s7
  -- 9. def:odd n := 2p + q², from 8
  exact ((Parley.Items.Stdlib.Divisibility.def_odd (n := 2 * p + q ^ 2))).mpr ⟨p + 2 * k ^ 2 + 2 * k, s8⟩

end Parley.Proofs.Hammack.PrimeSumOdd.PrimeSumOdd
