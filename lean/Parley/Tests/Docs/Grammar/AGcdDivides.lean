module

public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Divisibility

/-! Written from tests/docs/grammar.proof by parley build lean. -/

public section

namespace Parley.Tests.Docs.Grammar.AGcdDivides

theorem a_gcd_divides :
    (Int.gcd (4 : ℤ) (6 : ℤ) : ℤ) ∣ (4 : ℤ) := by
  -- 1. def:gcd a := 4, b := 6
  exact (Parley.Items.Stdlib.Divisibility.def_gcd_2 (a := (4 : ℤ)) (by norm_num) (b := (6 : ℤ)) (by norm_num))

end Parley.Tests.Docs.Grammar.AGcdDivides
