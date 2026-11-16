module

public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from tests/elaborator/pairs-compared.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.PairsCompared.APairOutsideAListOfPairs

theorem a_pair_outside_a_list_of_pairs :
    ¬ (((1 : ℤ), (2 : ℤ)) : ℤ × ℤ) ∈ ({((3 : ℤ), (4 : ℤ)), ((1 : ℤ), (5 : ℤ))} : Set (ℤ × ℤ)) := by
  -- 1. inspection
  simp

end Parley.Tests.Elaborator.PairsCompared.APairOutsideAListOfPairs
