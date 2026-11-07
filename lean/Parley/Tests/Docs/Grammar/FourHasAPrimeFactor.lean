module

public import ArithTactics
public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Prime
public import Parley.Items.Stdlib.Divisibility

/-! Written from tests/docs/grammar.proof by parley build lean. -/

public section

namespace Parley.Tests.Docs.Grammar.FourHasAPrimeFactor

theorem four_has_a_prime_factor :
    (∃ p : ℤ, 0 < p ∧ (Nat.Prime p.toNat ∧ p ∣ (4 : ℤ))) := by
  -- 1. thm:prime-factor m := 4
  have r36_1 : (4 : ℤ) > 1 := by parley_arith
  have s1 : ∃ p : ℤ, 0 < p ∧ (Nat.Prime p.toNat ∧ p ∣ (4 : ℤ)) := by exact (Parley.Items.Stdlib.Divisibility.thm_prime_factor (m := (4 : ℤ)) (by parley_side) (by parley_side))
  all_goals exact s1

end Parley.Tests.Docs.Grammar.FourHasAPrimeFactor
