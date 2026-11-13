module

public import Batteries.Util.ExtendedBinder
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from tests/elaborator/listed-numerals.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ListedNumerals.TheOddOnesCounted

theorem the_odd_ones_counted :
    ({x ∈ ({(2 : ℤ), (3 : ℤ), (7 : ℤ), (8 : ℤ)} : Set ℤ) | Odd x}.ncard : ℤ) = 2 := by
  -- 1. inspection
  rw [Set.ncard_eq_toFinset_card']; decide

end Parley.Tests.Elaborator.ListedNumerals.TheOddOnesCounted
