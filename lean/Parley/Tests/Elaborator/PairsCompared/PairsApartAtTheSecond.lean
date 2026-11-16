module

public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from tests/elaborator/pairs-compared.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.PairsCompared.PairsApartAtTheSecond

theorem pairs_apart_at_the_second :
    ¬ (((1 : ℤ), (1 : ℤ)) : ℤ × ℤ) = ((1 : ℤ), (2 : ℤ)) := by
  -- 1. arithmetic
  exact fun h => (show (1 : ℤ) ≠ 2 by norm_num) (congrArg Prod.snd h)

end Parley.Tests.Elaborator.PairsCompared.PairsApartAtTheSecond
