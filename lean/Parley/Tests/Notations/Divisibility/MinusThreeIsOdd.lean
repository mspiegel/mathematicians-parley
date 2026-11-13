module

public import ArithTactics
public import Tactics
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Divisibility

/-! Written from tests/notations/divisibility.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Divisibility.MinusThreeIsOdd

theorem minus_three_is_odd :
    Odd (-3 : ℤ) := by
  -- 1. arithmetic
  have s1 : (-3 : ℤ) = 2 * -2 + 1 := by parley_arith
  -- 2. def:odd n := −3, from 1
  exact ((Parley.Items.Stdlib.Divisibility.def_odd (n := (-3 : ℤ)))).mpr ⟨(-2 : ℤ), by norm_num⟩

end Parley.Tests.Notations.Divisibility.MinusThreeIsOdd
