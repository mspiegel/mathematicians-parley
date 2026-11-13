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

namespace Parley.Tests.Stdlib.Numbers.DifferenceNat0

theorem difference_nat0 (j : ℤ) (hH1 : 0 ≤ j) (k : ℤ) (hH2 : 0 ≤ k) (hH3 : j ≤ k) :
    0 ≤ k - j := by
  -- 1. mun:numbers-difference-nat0 m := j, n := k, from H3
  exact (Parley.Items.Stdlib.Numbers.mun_difference_nat0 (m := j) hH1 (n := k) hH2 hH3)

end Parley.Tests.Stdlib.Numbers.DifferenceNat0
