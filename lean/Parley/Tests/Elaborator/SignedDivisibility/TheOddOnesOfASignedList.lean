module

public import SetTactics
public import Tactics
public import Batteries.Util.ExtendedBinder
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Parity

/-! Written from tests/elaborator/signed-divisibility.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.SignedDivisibility.TheOddOnesOfASignedList

theorem the_odd_ones_of_a_signed_list :
    {x ∈ ({(-3 : ℤ), (-2 : ℤ), (0 : ℤ), (5 : ℤ)} : Set ℤ) | Odd x} = ({(-3 : ℤ), (5 : ℤ)} : Set ℤ) := by
  -- 1. inspection
  parley_set_side

end Parley.Tests.Elaborator.SignedDivisibility.TheOddOnesOfASignedList
