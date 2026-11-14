module

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
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Divisibility

/-! Written from tests/docs/grammar.proof by parley build lean. -/

public section

namespace Parley.Tests.Docs.Grammar.FourHasAPrimeFactor

theorem four_has_a_prime_factor :
    (∃ p : ℤ, 0 < p ∧ (Nat.Prime p.toNat ∧ p ∣ (4 : ℤ))) := by
  -- 1. thm:prime-factor m := 4
  have r36_1 : (4 : ℤ) > 1 := by norm_num
  exact (Parley.Items.Stdlib.Divisibility.thm_prime_factor (m := (4 : ℤ)) (by norm_num) (by norm_num))

end Parley.Tests.Docs.Grammar.FourHasAPrimeFactor
