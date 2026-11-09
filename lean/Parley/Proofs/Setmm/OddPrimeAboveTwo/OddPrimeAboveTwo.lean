module

public import OrderTactics
public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/setmm/odd-prime-above-two.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.OddPrimeAboveTwo.OddPrimeAboveTwo

theorem odd_prime_above_two (P : ℤ) (hH1 : 0 < P) (hH2 : Nat.Prime P.toNat) (hH3 : P ≠ 2) :
    2 < P := by
  -- 1. def:prime p := P, from H2
  have s1 : P > 1 := by exact (((Parley.Items.Stdlib.Divisibility.def_prime (p := P) (by parley_side))).mp hH2).1
  -- 2. mun:integer-step m := 1, n := P, from 1
  have s2 : 1 + 1 ≤ P := by exact (Parley.Items.Stdlib.Numbers.mun_integer_step (m := (1 : ℤ)) (n := P) s1)
  -- 3. inequalities, from H3, 2
  parley_order

end Parley.Proofs.Setmm.OddPrimeAboveTwo.OddPrimeAboveTwo
