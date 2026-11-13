module

public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/stdlib/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Numbers.NatPlusNat0

theorem nat_plus_nat0 (p : ℤ) (hH1 : 0 < p) (q : ℤ) (hH2 : 0 ≤ q) :
    0 < p + q := by
  -- 1. mun:numbers-nat-plus-nat0 a := p, b := q
  exact (Parley.Items.Stdlib.Numbers.mun_nat_plus_nat0 (a := p) hH1 (b := q) hH2)

end Parley.Tests.Stdlib.Numbers.NatPlusNat0
