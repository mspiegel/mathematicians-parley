module

public import ArithTactics
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from proofs/hammack/prime-between-ninety-and-a-hundred.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.PrimeBetweenNinetyAndAHundred.PrimeBetweenNinetyAndAHundred

theorem prime_between_ninety_and_a_hundred :
    (∃ p : ℤ, 0 < p ∧ ((Nat.Prime p.toNat ∧ 90 < p) ∧ p < 100)) := by
  -- 1. inspection
  have s1 : Nat.Prime (97 : ℤ).toNat := by norm_num
  -- 2. arithmetic
  have s2 : (90 : ℤ) < 97 := by parley_arith
  -- 3. arithmetic
  have s3 : (97 : ℤ) < 100 := by parley_arith
  -- 4. exhibit, from 1, 2, 3
  exact ⟨(97 : ℤ), by norm_num, ⟨⟨s1, by norm_num⟩, by norm_num⟩⟩

end Parley.Proofs.Hammack.PrimeBetweenNinetyAndAHundred.PrimeBetweenNinetyAndAHundred
