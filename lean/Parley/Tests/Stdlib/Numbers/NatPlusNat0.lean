module

public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/stdlib/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Numbers.NatPlusNat0

theorem nat_plus_nat0 (p : ℤ) (hH1 : 0 < p) (q : ℤ) (hH2 : 0 ≤ q) :
    0 < p + q := by
  -- 1. mun:numbers-nat-plus-nat0 a := p, b := q
  have s1 : 0 < p + q := by exact (Parley.Items.Stdlib.Numbers.mun_nat_plus_nat0 (a := p) (by parley_side) (b := q) (by parley_side))
  all_goals exact s1

end Parley.Tests.Stdlib.Numbers.NatPlusNat0
