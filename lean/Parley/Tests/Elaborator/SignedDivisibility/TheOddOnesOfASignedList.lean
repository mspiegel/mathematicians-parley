module

public import SetTactics
public import Tactics
public import Batteries.Util.ExtendedBinder
public import Mathlib.Algebra.Group.Int.Even
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Int.Parity
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Insert
public import Mathlib.Data.Set.Operations
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Parity

/-! Written from tests/elaborator/signed-divisibility.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.SignedDivisibility.TheOddOnesOfASignedList

theorem the_odd_ones_of_a_signed_list :
    {x ∈ ({(-3 : ℤ), (-2 : ℤ), (0 : ℤ), (5 : ℤ)} : Set ℤ) | Odd x} = ({(-3 : ℤ), (5 : ℤ)} : Set ℤ) := by
  -- 1. inspection
  ext x; simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Int.odd_iff, Int.even_iff]; omega

end Parley.Tests.Elaborator.SignedDivisibility.TheOddOnesOfASignedList
