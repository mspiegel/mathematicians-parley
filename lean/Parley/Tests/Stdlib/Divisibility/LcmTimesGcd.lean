module

public import Tactics
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Order.Lattice
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Divisibility

/-! Written from tests/stdlib/divisibility.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Divisibility.LcmTimesGcd

theorem lcm_times_gcd (a : ℤ) (b : ℤ) :
    (Int.lcm a b : ℤ) * (Int.gcd a b : ℤ) = abs (a * b) := by
  -- 1. mun:divisibility-lcm-times-gcd
  exact (Parley.Items.Stdlib.Divisibility.mun_lcm_times_gcd (a := a) (b := b))

end Parley.Tests.Stdlib.Divisibility.LcmTimesGcd
